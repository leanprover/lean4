// Lean compiler output
// Module: Lean.Elab.Util
// Imports: Init Lean.Parser.Command Lean.KeyedDeclsAttribute Lean.Elab.Exception
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1(lean_object*);
static lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__7;
static lean_object* l_Lean_Elab_expandMacroImpl_x3f___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__10;
static lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__19;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__20;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapter(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__3;
static lean_object* l_Lean_Elab_expandOptNamedPrio___closed__4;
lean_object* l_Lean_getRefPos___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__2;
lean_object* l_String_toFormat(lean_object*);
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__18;
lean_object* l_List_foldl___at_Lean_MacroScopesView_review___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
lean_object* l_Lean_log___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__23;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__2;
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addConstInfo___at_Lean_registerInitAttrUnsafe___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__15;
static lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__3;
lean_object* l_Lean_throwMaxRecDepthAt___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15;
static lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__9;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__12;
static lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__26;
static lean_object* l_Lean_Elab_expandOptNamedPrio___closed__5;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__11;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__4;
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__27;
static lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_expandOptNamedPrio___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Elab_Util___hyg_858_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__5;
static lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
static lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__16;
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__21;
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__17;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__12;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_pp_macroStack;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__5;
static lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__13;
static lean_object* l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__2;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__1;
static lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__3;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__8;
static lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2;
static lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__4;
static lean_object* l_Lean_Elab_expandOptNamedPrio___closed__3;
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_expandMacroImpl_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__25;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__7;
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376_(lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__9;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__14;
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__13;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__15;
static lean_object* l_Lean_Elab_getBetterRef___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__13;
lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object*);
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__2;
lean_object* l_Lean_isTracingEnabledFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__5;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__8;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__3;
static lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_toMessageList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__24;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__6;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__1;
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__1;
static lean_object* l_Lean_Elab_expandOptNamedPrio___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_expandMacroImpl_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__4;
lean_object* l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__4;
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__7;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__11;
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__2;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__14;
static lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__17;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_expandMacroImpl_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__17;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___auto____x40_Lean_Elab_Util___hyg_858____closed__18;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_prettyPrint(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Name_append(x_7, x_8);
x_10 = l_Lean_Name_append(x_9, x_5);
x_11 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_10, x_3);
x_12 = 1;
x_13 = l_Lean_Name_toString(x_11, x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Name_append(x_15, x_16);
x_18 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_17, x_3);
x_19 = 1;
x_20 = l_Lean_Name_toString(x_18, x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = 1;
x_24 = l_Lean_Name_toString(x_22, x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MacroScopesView_format(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_expandOptNamedPrio___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptNamedPrio___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptNamedPrio___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptNamedPrio___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namedPrio", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandOptNamedPrio___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__2;
x_3 = l_Lean_Elab_expandOptNamedPrio___closed__3;
x_4 = l_Lean_Elab_expandOptNamedPrio___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isNone(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_expandOptNamedPrio___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_expandOptNamedPrio(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Syntax_getPos_x3f(x_2, x_3);
x_5 = lean_box(0);
x_6 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1(x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_getBetterRef___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getBetterRef(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("macroStack", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("display macro expansion stack", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__3;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__5;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("while expanding", 15);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
x_7 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_MessageData_ofSyntax(x_9);
x_11 = l_Lean_indentD(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
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
x_1 = l_Lean_Elab_pp_macroStack;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with resulting expansion", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1;
x_6 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
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
lean_inc(x_13);
x_14 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__5;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_MessageData_ofSyntax(x_18);
x_20 = l_Lean_indentD(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_1);
x_5 = l_Lean_Parser_isValidSyntaxNodeKind(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2;
x_7 = l_Lean_throwError___rarg(x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKind___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_4);
x_9 = l_Lean_Name_append(x_5, x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Elab_checkSyntaxNodeKind___rarg(x_1, x_2, x_3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_7);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_3(x_12, lean_box(0), x_10, x_11);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2;
x_15 = l_Lean_throwError___rarg(x_1, x_3, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_1);
x_10 = l_Lean_Parser_isValidSyntaxNodeKind(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2;
x_12 = l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(x_11, x_2, x_3, x_8);
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
lean_inc(x_1);
x_16 = l_Lean_Parser_isValidSyntaxNodeKind(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2;
x_18 = l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(x_17, x_2, x_3, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_1, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Name_append(x_2, x_1);
x_9 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Exception_isRuntime(x_11);
if (x_13 == 0)
{
lean_free_object(x_9);
lean_dec(x_11);
x_2 = x_7;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
lean_free_object(x_9);
lean_dec(x_11);
x_2 = x_7;
x_5 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l_Lean_Exception_isRuntime(x_17);
if (x_19 == 0)
{
lean_dec(x_17);
x_2 = x_7;
x_5 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_dec(x_17);
x_2 = x_7;
x_5 = x_18;
goto _start;
}
}
}
}
}
default: 
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2;
x_25 = l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(x_24, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 6);
lean_inc(x_5);
x_6 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__1(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid syntax node kind '", 26);
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
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_7);
x_9 = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(x_7, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Exception_isRuntime(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
lean_dec(x_11);
lean_inc(x_7);
x_14 = l_Lean_Name_append(x_1, x_7);
x_15 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_14, x_3, x_4, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Exception_isRuntime(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
lean_dec(x_17);
x_20 = l_Lean_MessageData_ofName(x_7);
x_21 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_24, x_3, x_4, x_18);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_26 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
lean_dec(x_17);
x_27 = l_Lean_MessageData_ofName(x_7);
x_28 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_31, x_3, x_4, x_18);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = l_Lean_Exception_isRuntime(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
x_36 = l_Lean_MessageData_ofName(x_7);
x_37 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_40, x_3, x_4, x_34);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
x_44 = l_Lean_MessageData_ofName(x_7);
x_45 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_48, x_3, x_4, x_34);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
}
}
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_50 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_9);
lean_dec(x_11);
lean_inc(x_7);
x_51 = l_Lean_Name_append(x_1, x_7);
x_52 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_51, x_3, x_4, x_12);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_MessageData_ofName(x_7);
x_55 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_58, x_3, x_4, x_53);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_62 = l_Lean_Exception_isRuntime(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_inc(x_7);
x_63 = l_Lean_Name_append(x_1, x_7);
x_64 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_63, x_3, x_4, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l_Lean_Exception_isRuntime(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
lean_dec(x_65);
x_69 = l_Lean_MessageData_ofName(x_7);
x_70 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_73, x_3, x_4, x_66);
lean_dec(x_4);
lean_dec(x_3);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_66);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_67);
lean_dec(x_65);
x_77 = l_Lean_MessageData_ofName(x_7);
x_78 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_81, x_3, x_4, x_66);
lean_dec(x_4);
lean_dec(x_3);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_60);
lean_ctor_set(x_84, 1, x_61);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_60);
lean_inc(x_7);
x_85 = l_Lean_Name_append(x_1, x_7);
x_86 = l_Lean_Elab_checkSyntaxNodeKind___at_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___spec__2(x_85, x_3, x_4, x_61);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_MessageData_ofName(x_7);
x_89 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_92, x_3, x_4, x_87);
lean_dec(x_4);
lean_dec(x_3);
return x_93;
}
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_6);
if (x_94 == 0)
{
return x_6;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_6, 0);
x_96 = lean_ctor_get(x_6, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_6);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_syntaxNodeKindOfAttrParam___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Syntax", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2;
x_5 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__2;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__1;
x_4 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__2;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__1;
x_4 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exact", 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__2;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__1;
x_4 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__4;
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declName", 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__2;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__13;
x_4 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decl_name%", 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__16;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__4;
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__15;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__18;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__12;
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__10;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__20;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__4;
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__8;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__22;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__4;
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__23;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__6;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__24;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__4;
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__25;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__3;
x_3 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__26;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Elab_Util___hyg_858_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Elab_Util___hyg_858____closed__27;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 6);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
x_19 = l_Lean_Environment_contains(x_13, x_8);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_14);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_3, x_21);
lean_dec(x_3);
x_23 = lean_box(0);
lean_inc(x_8);
x_24 = l_Lean_Elab_addConstInfo___at_Lean_registerInitAttrUnsafe___spec__13(x_22, x_8, x_23, x_4, x_5, x_17);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_ctor_get(x_33, 6);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_8);
x_36 = l_Lean_Environment_contains(x_13, x_8);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
lean_dec(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_3, x_40);
lean_dec(x_3);
x_42 = lean_box(0);
lean_inc(x_8);
x_43 = l_Lean_Elab_addConstInfo___at_Lean_registerInitAttrUnsafe___spec__13(x_41, x_8, x_42, x_4, x_5, x_34);
lean_dec(x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_8);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
return x_7;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declRange", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("addBuiltinDeclarationRanges", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("DeclarationRanges", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__6;
x_3 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("DeclarationRange", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__10;
x_3 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Position", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__13;
x_3 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__2;
lean_inc(x_1);
x_17 = l_Lean_Name_append(x_1, x_16);
x_18 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = l_Lean_mkNatLit(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_mkNatLit(x_23);
x_25 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16;
x_26 = lean_array_push(x_25, x_22);
x_27 = lean_array_push(x_26, x_24);
x_28 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__15;
x_29 = l_Lean_mkAppN(x_28, x_27);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
x_31 = l_Lean_mkNatLit(x_30);
x_32 = lean_ctor_get(x_19, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = l_Lean_mkNatLit(x_33);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_array_push(x_25, x_34);
x_38 = lean_array_push(x_37, x_36);
x_39 = l_Lean_mkAppN(x_28, x_38);
x_40 = lean_ctor_get(x_19, 3);
lean_inc(x_40);
lean_dec(x_19);
x_41 = l_Lean_mkNatLit(x_40);
x_42 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__17;
x_43 = lean_array_push(x_42, x_29);
x_44 = lean_array_push(x_43, x_31);
x_45 = lean_array_push(x_44, x_39);
x_46 = lean_array_push(x_45, x_41);
x_47 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__12;
x_48 = l_Lean_mkAppN(x_47, x_46);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = l_Lean_mkNatLit(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_array_push(x_25, x_52);
x_56 = lean_array_push(x_55, x_54);
x_57 = l_Lean_mkAppN(x_28, x_56);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
x_59 = l_Lean_mkNatLit(x_58);
x_60 = lean_ctor_get(x_49, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = l_Lean_mkNatLit(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_mkNatLit(x_63);
x_65 = lean_array_push(x_25, x_62);
x_66 = lean_array_push(x_65, x_64);
x_67 = l_Lean_mkAppN(x_28, x_66);
x_68 = lean_ctor_get(x_49, 3);
lean_inc(x_68);
lean_dec(x_49);
x_69 = l_Lean_mkNatLit(x_68);
x_70 = lean_array_push(x_42, x_57);
x_71 = lean_array_push(x_70, x_59);
x_72 = lean_array_push(x_71, x_67);
x_73 = lean_array_push(x_72, x_69);
x_74 = l_Lean_mkAppN(x_47, x_73);
x_75 = lean_array_push(x_25, x_48);
x_76 = lean_array_push(x_75, x_74);
x_77 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__9;
x_78 = l_Lean_mkAppN(x_77, x_76);
x_79 = lean_array_push(x_25, x_18);
x_80 = lean_array_push(x_79, x_78);
x_81 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__5;
x_82 = l_Lean_mkAppN(x_81, x_80);
x_83 = l_Lean_declareBuiltin(x_17, x_82, x_3, x_4, x_14);
return x_83;
}
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docString", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("addBuiltinDocString", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
lean_inc(x_2);
x_13 = l_Lean_findDocString_x3f(x_11, x_2, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3(x_2, x_16, x_3, x_4, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__2;
lean_inc(x_2);
x_21 = l_Lean_Name_append(x_2, x_20);
lean_inc(x_2);
x_22 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_2);
x_23 = l_Lean_mkStrLit(x_19);
x_24 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16;
x_25 = lean_array_push(x_24, x_22);
x_26 = lean_array_push(x_25, x_23);
x_27 = l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__5;
x_28 = l_Lean_mkAppN(x_27, x_26);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_declareBuiltin(x_21, x_28, x_3, x_4, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3(x_2, x_30, x_3, x_4, x_31);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" elaborator", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__4___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
x_9 = lean_string_append(x_5, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed), 6, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l_Lean_Elab_mkElabAttribute___rarg___closed__2;
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = l_Lean_KeyedDeclsAttribute_init___rarg(x_12, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_mkElabAttribute___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Elab_mkElabAttribute___rarg___lambda__2(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_mkElabAttribute___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_mkElabAttribute___rarg___lambda__4(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("builtin_macro", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("macro", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Macro", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
x_4 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__4;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__6;
x_7 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_3, x_4, x_5, x_6, x_7, x_1, x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("macroAttribute", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__2;
x_3 = l_Lean_Elab_mkMacroAttributeUnsafe(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_expandMacroImpl_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_ctor_set(x_6, 0, x_14);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 3);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_5, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
lean_inc(x_1);
x_21 = lean_apply_3(x_10, x_1, x_20, x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
return x_42;
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_21, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
lean_dec(x_8);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_53);
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_ctor_get(x_8, 0);
lean_inc(x_55);
lean_dec(x_8);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_43);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_8);
x_64 = lean_ctor_get(x_21, 1);
lean_inc(x_64);
lean_dec(x_21);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_5 = x_64;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_6, 0);
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_6);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_66, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_ctor_get(x_5, 0);
x_72 = lean_ctor_get(x_5, 1);
x_73 = lean_ctor_get(x_5, 3);
x_74 = lean_ctor_get(x_5, 4);
x_75 = lean_ctor_get(x_5, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_66);
lean_ctor_set(x_76, 3, x_73);
lean_ctor_set(x_76, 4, x_74);
lean_ctor_set(x_76, 5, x_75);
lean_inc(x_1);
x_77 = lean_apply_3(x_10, x_1, x_76, x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_8, 0);
lean_inc(x_81);
lean_dec(x_8);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_80)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_80;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_79);
return x_89;
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_92 = x_77;
} else {
 lean_dec_ref(x_77);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_8, 0);
lean_inc(x_93);
lean_dec(x_8);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
if (lean_is_scalar(x_92)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_92;
 lean_ctor_set_tag(x_101, 0);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_91);
return x_101;
}
else
{
lean_object* x_102; 
lean_dec(x_8);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
lean_dec(x_77);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_5 = x_102;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_expandMacroImpl_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_expandMacroImpl_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_5 = l_Lean_Syntax_getKind(x_2);
x_6 = l_Lean_Elab_expandMacroImpl_x3f___closed__1;
x_7 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_6, x_1, x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Elab_expandMacroImpl_x3f___closed__2;
x_10 = l_List_forIn_loop___at_Lean_Elab_expandMacroImpl_x3f___spec__1(x_2, x_9, x_7, x_9, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_expandMacroImpl_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Elab_expandMacroImpl_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapter___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
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
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_addTrace___rarg(x_1, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
lean_closure_set(x_16, 7, x_14);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
lean_inc(x_17);
lean_inc(x_1);
x_19 = l_Lean_isTracingEnabledFor___rarg(x_1, x_3, x_5, x_17);
x_20 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_7);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_17);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_21, x_16);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_3);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_3);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_3);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_3);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_3);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_3);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_List_reverse___rarg(x_11);
lean_inc(x_7);
lean_inc(x_2);
x_13 = l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__5___boxed), 3, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_9);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_22 = lean_apply_2(x_7, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_apply_1(x_25, x_26);
lean_inc(x_14);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__6___boxed), 10, 9);
lean_closure_set(x_28, 0, x_24);
lean_closure_set(x_28, 1, x_9);
lean_closure_set(x_28, 2, x_10);
lean_closure_set(x_28, 3, x_11);
lean_closure_set(x_28, 4, x_12);
lean_closure_set(x_28, 5, x_13);
lean_closure_set(x_28, 6, x_14);
lean_closure_set(x_28, 7, x_15);
lean_closure_set(x_28, 8, x_23);
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
lean_dec(x_10);
lean_dec(x_8);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_maxRecDepthErrorMessage;
x_34 = lean_string_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_throwErrorAt___rarg(x_9, x_16, x_31, x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_9);
x_38 = l_Lean_throwMaxRecDepthAt___rarg(x_16, x_31);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
lean_dec(x_16);
x_40 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__7___boxed), 17, 16);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_1);
lean_closure_set(x_18, 8, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__8), 16, 15);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__9), 16, 15);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__10), 15, 14);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1), 4, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_15, 0, x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 4, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_13);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__4___boxed), 6, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_inc(x_12);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__11), 14, 13);
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
lean_closure_set(x_22, 10, x_12);
lean_closure_set(x_22, 11, x_20);
lean_closure_set(x_22, 12, x_3);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__12), 13, 12);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__13), 13, 12);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__14), 12, 11);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_1);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_9);
lean_closure_set(x_14, 9, x_10);
lean_closure_set(x_14, 10, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_List_forM___at_Lean_Elab_liftMacroM___spec__3___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___rarg___lambda__5(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__7___boxed(lean_object** _args) {
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
x_18 = l_Lean_Elab_liftMacroM___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_apply_1(x_11, x_12);
x_14 = l_Lean_Elab_liftMacroM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = lean_name_append_index_after(x_1, x_3);
lean_inc(x_6);
lean_inc(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_5);
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
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal exception: ", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = l_Lean_MessageData_ofName(x_5);
x_7 = l_Lean_Elab_logException___rarg___lambda__1___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_logException___rarg___lambda__1___closed__4;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 2;
x_12 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 2;
x_10 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_Elab_isAbortExceptionId(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(x_14, 0, x_11);
x_15 = lean_apply_2(x_5, lean_box(0), x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_logException___rarg___lambda__1), 5, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logException___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_logException___rarg), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_apply_3(x_8, lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_5 = l_Lean_FileMap_toPosition(x_4, x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = l_Nat_repr(x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Elab_logException___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Nat_repr(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Exception_toMessageData(x_3);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
x_26 = lean_apply_2(x_7, lean_box(0), x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Exception_getRef(x_1);
x_7 = 0;
x_8 = l_Lean_Syntax_getPos_x3f(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Exception_toMessageData(x_1);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_1);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Exception_toMessageData(x_1);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_getRefPos___rarg(x_1, x_2);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = lean_array_uset(x_2, x_1, x_6);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_nestedExceptionToMessageData___rarg(x_1, x_2, x_10);
x_15 = lean_box_usize(x_4);
x_16 = lean_box_usize(x_3);
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_2);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", errors ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Elab_logException___rarg___lambda__1___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_toMessageList(x_4);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = l_Lean_throwError___rarg(x_2, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
lean_inc(x_2);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg(x_2, x_3, x_8, x_9, x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_1);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_throwErrorWithNestedErrors___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__2;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__3;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__5;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__7;
x_2 = l_Lean_Elab_expandOptNamedPrio___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__8;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Util", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__9;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__11;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__13;
x_2 = lean_unsigned_to_nat(2999u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__17;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__1;
x_3 = 0;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__14;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__16;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__18;
x_11 = 1;
x_12 = l_Lean_registerTraceClass(x_10, x_11, x_4, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_expandOptNamedPrio___closed__1 = _init_l_Lean_Elab_expandOptNamedPrio___closed__1();
lean_mark_persistent(l_Lean_Elab_expandOptNamedPrio___closed__1);
l_Lean_Elab_expandOptNamedPrio___closed__2 = _init_l_Lean_Elab_expandOptNamedPrio___closed__2();
lean_mark_persistent(l_Lean_Elab_expandOptNamedPrio___closed__2);
l_Lean_Elab_expandOptNamedPrio___closed__3 = _init_l_Lean_Elab_expandOptNamedPrio___closed__3();
lean_mark_persistent(l_Lean_Elab_expandOptNamedPrio___closed__3);
l_Lean_Elab_expandOptNamedPrio___closed__4 = _init_l_Lean_Elab_expandOptNamedPrio___closed__4();
lean_mark_persistent(l_Lean_Elab_expandOptNamedPrio___closed__4);
l_Lean_Elab_expandOptNamedPrio___closed__5 = _init_l_Lean_Elab_expandOptNamedPrio___closed__5();
lean_mark_persistent(l_Lean_Elab_expandOptNamedPrio___closed__5);
l_Lean_Elab_getBetterRef___closed__1 = _init_l_Lean_Elab_getBetterRef___closed__1();
lean_mark_persistent(l_Lean_Elab_getBetterRef___closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376____closed__7);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_376_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_pp_macroStack = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_pp_macroStack);
lean_dec_ref(res);
}l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1 = _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1();
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
l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__4);
l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__5 = _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__5);
l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__1);
l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___rarg___lambda__1___closed__2);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4);
l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1 = _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1);
l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2 = _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__1 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__1);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__2 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__2);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__3 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__3);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__4 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__4);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__5 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__5);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__6 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__6);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__7 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__7);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__8 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__8);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__9 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__9);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__10 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__10);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__11 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__11);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__12 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__12);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__13 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__13);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__14 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__14);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__15 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__15);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__16 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__16);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__17 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__17);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__18 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__18);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__19 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__19);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__20 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__20);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__21 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__21);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__22 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__22);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__23 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__23);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__24 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__24);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__25 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__25);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__26 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__26();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__26);
l___auto____x40_Lean_Elab_Util___hyg_858____closed__27 = _init_l___auto____x40_Lean_Elab_Util___hyg_858____closed__27();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858____closed__27);
l___auto____x40_Lean_Elab_Util___hyg_858_ = _init_l___auto____x40_Lean_Elab_Util___hyg_858_();
lean_mark_persistent(l___auto____x40_Lean_Elab_Util___hyg_858_);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__1);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__2 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__2);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__3 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__3);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__4 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__4);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__5 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__5);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__6 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__6);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__7);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__8 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__8);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__9 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__9);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__10 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__10);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__11 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__11);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__12 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__12);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__13 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__13);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__14 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__14);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__15 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__15);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__16);
l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__17 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__3___closed__17);
l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__1);
l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__2 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__2);
l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__3 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__3);
l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__4 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__4);
l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__5 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__4___closed__5);
l_Lean_Elab_mkElabAttribute___rarg___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___closed__1);
l_Lean_Elab_mkElabAttribute___rarg___closed__2 = _init_l_Lean_Elab_mkElabAttribute___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___closed__2);
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
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393____closed__2);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1393_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_macroAttribute);
lean_dec_ref(res);
}l_Lean_Elab_expandMacroImpl_x3f___closed__1 = _init_l_Lean_Elab_expandMacroImpl_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_expandMacroImpl_x3f___closed__1);
l_Lean_Elab_expandMacroImpl_x3f___closed__2 = _init_l_Lean_Elab_expandMacroImpl_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_expandMacroImpl_x3f___closed__2);
l_Lean_Elab_logException___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__1);
l_Lean_Elab_logException___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__2);
l_Lean_Elab_logException___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__3);
l_Lean_Elab_logException___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__4);
l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__1);
l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__2);
l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__3);
l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___rarg___lambda__1___closed__4);
l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__1);
l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_throwErrorWithNestedErrors___rarg___lambda__1___closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__16);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__17 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__17();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__17);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__18 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__18();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999____closed__18);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_2999_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
