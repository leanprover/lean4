// Lean compiler output
// Module: Lean.Parser.Extension
// Imports: Init Lean.Parser.Basic Lean.Parser.StrInterpolation Lean.KeyedDeclsAttribute
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
lean_object* l_Lean_Parser_builtinTokenTable;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens_match__1(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__5;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__1(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__2;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingIdentAsSymbol___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByTermToken___closed__1;
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserContext(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__1;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeHooks(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__2;
lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder_match__1(lean_object*);
lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__3;
lean_object* l_List_foldlM___main___at_Lean_Parser_addParserTokens___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Parser_mkParserAttributeHooks___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
extern lean_object* l_Lean_Parser_charLit;
lean_object* l_Lean_Parser_mkParserOfConstantAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig_match__1(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
lean_object* l_Lean_Parser_parserExtension___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_getTokenTable___boxed(lean_object*);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__1(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__3(lean_object*);
extern lean_object* l_Lean_registerInternalExceptionId___closed__2;
lean_object* l_Lean_Parser_addParser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_categoryParserFnRef;
lean_object* l_Lean_Parser_compileParserDescr_visit_match__1(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser_match__2___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Parser_builtinParserCategoriesRef;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_parserExtension___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getParserPriority_match__2(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserExtensionState_newEntries___default;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__1;
lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_Lean_Parser_notFollowedByCommandToken___closed__1;
lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Lean_Parser_Basic___instance__8___closed__1;
extern lean_object* l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__4;
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__2(lean_object*);
lean_object* l_Lean_Parser_notFollowedByCommandToken___closed__2;
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__4___rarg(lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__8;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_22____spec__1(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__2;
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Parser_addTrailingParser_match__1(lean_object*);
lean_object* l_Lean_Parser_parserExtension___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__4;
extern lean_object* l_Lean_nameLitKind;
lean_object* l_Lean_Parser_getParserPriority_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__3(lean_object*);
lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Lean_Parser_Extension___instance__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addParserCategory(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_many1Fn(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser_match__1(lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__2;
lean_object* l_Lean_Parser_parserExtension___closed__3;
lean_object* l_Lean_Parser_parserExtension___elambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
lean_object* l_Lean_Parser_parserExtension___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__2(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__3;
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object*);
uint8_t l_Lean_Parser_leadingIdentAsSymbol(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__1;
extern lean_object* l_Lean_mkAttributeImplOfConstant___closed__1;
lean_object* l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(lean_object*);
lean_object* l_Lean_Parser_getParserPriority_match__1(lean_object*);
lean_object* l_List_forM___main___at_Lean_Parser_runParserAttributeHooks___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setCategoryParserFnRef(lean_object*);
lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__3;
lean_object* l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__3;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__1;
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__8;
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object*);
lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Parser_categoryParserFnImpl___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__6;
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(lean_object*, size_t, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_declareBuiltin___rarg___closed__6;
lean_object* l_Lean_Parser_categoryParserFnImpl___closed__2;
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__5;
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__9;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__1;
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser(lean_object*);
lean_object* l_Lean_Parser_notFollowedByTermToken___closed__2;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_98_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_49_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_22_(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addParser_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Trie_Lean_Data_Trie___instance__1___closed__1;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
uint8_t l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__2;
lean_object* l_Lean_Parser_parserExtension___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__4;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2;
lean_object* l_Lean_Parser_parserExtension___elambda__4(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__4(lean_object*);
lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__1;
lean_object* l_Lean_Parser_compileParserDescr_visit_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__2(lean_object*);
lean_object* l_Lean_Name_toExprAux(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addToken(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__3;
lean_object* l_Lean_Parser_categoryParserFnImpl___closed__4;
lean_object* l_Lean_Parser_notFollowedByCategoryToken(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit_match__3(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Parser_runParserAttributeHooks___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__5;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
lean_object* l_Lean_Parser_mkParserAttributeImpl___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(lean_object*);
extern lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__1;
lean_object* l_Lean_Parser_compileParserDescr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setCategoryParserFnRef___closed__1;
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
extern lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
lean_object* l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__2(lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__1;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__2;
lean_object* l_Lean_Parser_Trie_insert_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getCategory___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingIdentAsSymbol_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getParserPriority___closed__4;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFnImpl_match__1(lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Parser_addParser_match__1(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getParserPriority___closed__2;
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__2;
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__6___closed__2;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Parser_parserExtension___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__6;
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getParserPriority___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__1(lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_13__quoteName___main___closed__2;
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFnImpl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_Error_Init_System_IOError___instance__2___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3;
extern lean_object* l_Lean_Lean_ToExpr___instance__7___closed__1;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern lean_object* l_Lean_Parser_numLit;
uint8_t l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__7;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__5___closed__2;
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__3;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg(lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__2(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1;
lean_object* l_Lean_Parser_tryFn(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_List_foldl___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_98____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFnImpl___closed__3;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser_match__1(lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l_Lean_Parser_parserAttributeHooks;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__3;
lean_object* l_Lean_Parser_notFollowedByTermToken;
lean_object* l_Lean_Parser_addTrailingParser_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingIdentAsSymbol_match__1(lean_object*);
extern lean_object* l_Lean_regularInitAttr;
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__5;
lean_object* l_Lean_Parser_getParserPriority(lean_object*);
lean_object* l_Lean_Parser_builtinSyntaxNodeKindSetRef;
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState___boxed(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__2;
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__2;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__1;
lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__1;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByCommandToken;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_match__1(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__1;
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserExtensionState_categories___default;
lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* lean_st_ref_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit_match__3___rarg___boxed(lean_object**);
lean_object* l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(lean_object*);
lean_object* l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__1(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object*);
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_addParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_match__1(lean_object*);
lean_object* l_Lean_Parser_compileParserDescr_visit___closed__7;
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser_match__2(lean_object*);
lean_object* l_Lean_Parser_getParserPriority___closed__3;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__2(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__3(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__6;
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserExtensionState_kinds___default;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__2;
lean_object* l_Lean_Parser_getParserPriority___closed__5;
extern lean_object* l_Lean_Parser_mkAntiquot___closed__8;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__2___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getSyntaxNodeKinds___boxed(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_KeyedDeclsAttribute_declareBuiltin___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getParserPriority_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addParser_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__3;
lean_object* l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
extern lean_object* l_Lean_Parser_Lean_Parser_Basic___instance__14___closed__1;
lean_object* l_Lean_Parser_Trie_find_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getCategory(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__1;
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2;
extern lean_object* l_Lean_Parser_strLit;
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserExtensionState_tokens___default;
lean_object* l_Lean_Parser_compileParserDescr_visit_match__2(lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1;
lean_object* l_Lean_Parser_parserExtension___elambda__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__2;
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4;
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Lean_Parser_Extension___instance__1___closed__1;
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4____spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_Trie_Lean_Data_Trie___instance__1___closed__1;
x_3 = l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_22____spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_22_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_3 = l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_22____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
x_4 = lean_st_ref_take(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_5, x_1, x_7);
x_9 = lean_st_ref_set(x_3, x_8, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_choiceKind;
x_3 = l_Lean_Parser_registerBuiltinNodeKind(x_2, x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_identKind;
x_6 = l_Lean_Parser_registerBuiltinNodeKind(x_5, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_strLitKind;
x_9 = l_Lean_Parser_registerBuiltinNodeKind(x_8, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_numLitKind;
x_12 = l_Lean_Parser_registerBuiltinNodeKind(x_11, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_charLitKind;
x_15 = l_Lean_Parser_registerBuiltinNodeKind(x_14, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_nameLitKind;
x_18 = l_Lean_Parser_registerBuiltinNodeKind(x_17, x_16);
return x_18;
}
}
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_98____spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_98_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_3 = l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_98____spec__1(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser category '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been defined");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg), 1, 0);
return x_2;
}
}
uint8_t l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
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
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
uint8_t l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_93 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(x_3, x_90, x_91, x_90, x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_107 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(x_3, x_104, x_105, x_104, x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_1);
x_4 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg(x_2);
return x_7;
}
}
}
lean_object* l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Parser_builtinParserCategoriesRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Parser_Lean_Parser_Basic___instance__14___closed__1;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_2);
x_10 = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(x_6, x_1, x_9);
x_11 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_10, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_set(x_4, x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtensionState_tokens___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Trie_Lean_Data_Trie___instance__1___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtensionState_kinds___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtensionState_categories___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtensionState_newEntries___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Lean_Parser_Extension___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Trie_Lean_Data_Trie___instance__1___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Lean_Parser_Extension___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Lean_Parser_Extension___instance__1___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = l_Lean_Parser_builtinTokenTable;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Parser_builtinParserCategoriesRef;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid empty symbol");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_6 = l_Lean_Parser_Trie_find_x3f_loop___rarg(x_2, x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l_Lean_Parser_Trie_insert_loop___rarg(x_2, x_2, x_1, x_5);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2;
return x_10;
}
}
}
static lean_object* _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown parser category '");
return x_1;
}
}
lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Char_HasRepr___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_throwUnknownParserCategory___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_getCategory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_getCategory___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_getCategory(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_addLeadingParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Parser_addLeadingParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_addLeadingParser_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_addLeadingParser_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_addLeadingParser_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_addLeadingParser_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_box(0);
x_7 = lean_name_mk_string(x_6, x_4);
x_8 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_name_mk_string(x_11, x_9);
x_13 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Parser_TokenMap_insert___rarg(x_8, x_5, x_9);
lean_ctor_set(x_3, 0, x_10);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lean_Parser_TokenMap_insert___rarg(x_12, x_5, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
x_3 = x_18;
x_4 = x_6;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Parser_TokenMap_insert___rarg(x_8, x_5, x_9);
lean_ctor_set(x_3, 0, x_10);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lean_Parser_TokenMap_insert___rarg(x_12, x_5, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
x_3 = x_18;
x_4 = x_6;
goto _start;
}
}
}
}
lean_object* l_Lean_Parser_addLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
switch (lean_obj_tag(x_9)) {
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(x_11);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_12);
x_16 = l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__2(x_4, x_5, x_14, x_15);
lean_ctor_set(x_10, 0, x_16);
x_17 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_19);
lean_dec(x_10);
x_21 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_12);
x_22 = l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__2(x_4, x_5, x_19, x_21);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_20);
x_24 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(x_27);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_28);
x_32 = l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__3(x_4, x_5, x_30, x_31);
lean_ctor_set(x_26, 0, x_32);
x_33 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_26);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_26);
x_37 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_28);
x_38 = l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__3(x_4, x_5, x_35, x_37);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_36);
x_40 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
default: 
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_9);
x_42 = lean_ctor_get(x_6, 0);
lean_inc(x_42);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 3);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_44, 1);
x_51 = lean_ctor_get(x_44, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_44, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_44, 0);
lean_dec(x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_44, 1, x_54);
x_55 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_42);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set(x_59, 3, x_47);
lean_ctor_set(x_42, 0, x_59);
x_60 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_42);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 3);
lean_inc(x_66);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_5);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 4, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_65);
lean_ctor_set(x_71, 3, x_66);
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_63);
x_73 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
}
}
lean_object* l_Lean_Parser_addLeadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_addLeadingParser(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Parser_TokenMap_insert___rarg(x_8, x_5, x_9);
lean_ctor_set(x_3, 2, x_10);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lean_Parser_TokenMap_insert___rarg(x_14, x_5, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
x_3 = x_18;
x_4 = x_6;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Parser_TokenMap_insert___rarg(x_8, x_5, x_9);
lean_ctor_set(x_3, 2, x_10);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lean_Parser_TokenMap_insert___rarg(x_14, x_5, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
x_3 = x_18;
x_4 = x_6;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
switch (lean_obj_tag(x_5)) {
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(x_6);
x_8 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_7);
x_9 = l_List_foldl___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__1(x_2, x_3, x_1, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__1(x_10);
x_12 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_11);
x_13 = l_List_foldl___main___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__2(x_2, x_3, x_1, x_12);
return x_13;
}
default: 
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_1, 3, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_Parser_addTrailingParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_addTrailingParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_addTrailingParser_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_addTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(x_9, x_3, x_4);
lean_ctor_set(x_7, 0, x_10);
x_11 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(x_13, x_3, x_4);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
x_17 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_addParser_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
}
}
lean_object* l_Lean_Parser_addParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_addParser_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_addParser_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_addParser_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_addParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Parser_addTrailingParser(x_1, x_2, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Parser_addLeadingParser(x_1, x_2, x_3, x_5, x_6);
return x_8;
}
}
}
lean_object* l_Lean_Parser_addParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Parser_addParser(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_List_foldlM___main___at_Lean_Parser_addParserTokens___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
}
}
}
lean_object* l_Lean_Parser_addParserTokens(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
x_6 = l_List_foldlM___main___at_Lean_Parser_addParserTokens___spec__1(x_1, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin parser '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', ");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Parser_builtinTokenTable;
x_5 = l_Lean_Parser_Trie_Lean_Data_Trie___instance__1___closed__1;
x_6 = lean_st_ref_swap(x_4, x_5, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Parser_addParserTokens(x_8, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_2);
x_14 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = l_String_splitAux___main___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_6);
lean_dec(x_2);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_st_ref_set(x_4, x_22, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_30 = l_Lean_Parser_addParserTokens(x_28, x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_System_FilePath_dirName___closed__1;
x_33 = l_Lean_Name_toStringWithSep___main(x_32, x_2);
x_34 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_31);
lean_dec(x_31);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_st_ref_set(x_4, x_43, x_29);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Parser_builtinParserCategoriesRef;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_11 = l_Lean_Parser_addParser(x_9, x_1, x_2, x_3, x_4, x_5);
x_12 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_11, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_set(x_7, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
x_20 = lean_st_ref_take(x_19, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_1(x_18, x_21);
x_24 = lean_st_ref_set(x_19, x_23, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(x_17, x_2, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_apply_2(x_4, x_10, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_box(x_16);
x_20 = lean_apply_5(x_5, x_14, x_15, x_19, x_17, x_18);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry_match__3___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.Extension");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Parser.Extension.0.Lean.Parser.ParserExtensionAddEntry");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2;
x_3 = lean_unsigned_to_nat(153u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2;
x_3 = lean_unsigned_to_nat(164u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_9 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_5, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_10 = l_Lean_Parser_Lean_Parser_Extension___instance__1;
x_11 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_3);
x_20 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_16, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_21 = l_Lean_Parser_Lean_Parser_Extension___instance__1;
x_22 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3;
x_23 = lean_panic_fn(x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_box(0);
lean_inc(x_28);
x_33 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_30, x_28, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_1, 3, x_35);
lean_ctor_set(x_1, 1, x_33);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_40 = lean_box(0);
lean_inc(x_28);
x_41 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_37, x_28, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_43);
return x_44;
}
}
case 2:
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 3);
lean_inc(x_50);
lean_inc(x_49);
x_51 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_49, x_45);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_1, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_1, 0);
lean_dec(x_56);
x_57 = l_Lean_Parser_Lean_Parser_Basic___instance__14___closed__1;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_46);
lean_inc(x_45);
x_59 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_49, x_45, x_58);
x_60 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_1, 3, x_61);
lean_ctor_set(x_1, 2, x_59);
return x_1;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_62 = l_Lean_Parser_Lean_Parser_Basic___instance__14___closed__1;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_46);
lean_inc(x_45);
x_64 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_49, x_45, x_63);
x_65 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_65, 0, x_45);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_46);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_47);
lean_ctor_set(x_67, 1, x_48);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_66);
return x_67;
}
}
else
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_45);
return x_1;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_71 = lean_ctor_get(x_2, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_72);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_1, 1);
x_76 = lean_ctor_get(x_1, 2);
x_77 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
lean_inc(x_68);
x_78 = l_Lean_Parser_addParser(x_76, x_68, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
lean_free_object(x_1);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_79 = l_Lean_Parser_Lean_Parser_Extension___instance__1;
x_80 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4;
x_81 = lean_panic_fn(x_79, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_69);
lean_ctor_set(x_83, 2, x_72);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set(x_1, 2, x_82);
return x_1;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_1, 0);
x_86 = lean_ctor_get(x_1, 1);
x_87 = lean_ctor_get(x_1, 2);
x_88 = lean_ctor_get(x_1, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_1);
lean_inc(x_72);
lean_inc(x_68);
x_89 = l_Lean_Parser_addParser(x_87, x_68, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_90 = l_Lean_Parser_Lean_Parser_Extension___instance__1;
x_91 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4;
x_92 = lean_panic_fn(x_90, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_94, 0, x_68);
lean_ctor_set(x_94, 1, x_69);
lean_ctor_set(x_94, 2, x_72);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_88);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_85);
lean_ctor_set(x_96, 1, x_86);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_95);
return x_96;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParserDescr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
uint64_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get_usize(x_7, 2);
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get_usize(x_8, 2);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = l_Lean_mkAppStx___closed__1;
x_21 = lean_string_dec_eq(x_17, x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_6, x_1);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
x_27 = lean_string_dec_eq(x_13, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
x_28 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
x_29 = lean_string_dec_eq(x_13, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_5);
lean_ctor_set(x_8, 1, x_20);
x_30 = lean_apply_1(x_6, x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_1);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_6);
x_31 = lean_box_uint64(x_12);
x_32 = lean_box_usize(x_18);
x_33 = lean_box_usize(x_14);
x_34 = lean_apply_4(x_5, x_10, x_31, x_32, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_1);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_box_uint64(x_12);
x_36 = lean_box_usize(x_18);
x_37 = lean_box_usize(x_14);
x_38 = lean_apply_4(x_4, x_10, x_35, x_36, x_37);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_1);
x_39 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
x_40 = lean_string_dec_eq(x_13, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_4);
x_41 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
x_42 = lean_string_dec_eq(x_13, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_ctor_set(x_8, 1, x_20);
x_43 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set_uint64(x_43, sizeof(void*)*2, x_12);
x_44 = lean_apply_1(x_6, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_6);
x_45 = lean_box_uint64(x_12);
x_46 = lean_box_usize(x_18);
x_47 = lean_box_usize(x_14);
x_48 = lean_apply_4(x_5, x_10, x_45, x_46, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_49 = lean_box_uint64(x_12);
x_50 = lean_box_usize(x_18);
x_51 = lean_box_usize(x_14);
x_52 = lean_apply_4(x_4, x_10, x_49, x_50, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_8, 1);
x_54 = lean_ctor_get_usize(x_8, 2);
lean_inc(x_53);
lean_dec(x_8);
x_55 = l_Lean_mkAppStx___closed__1;
x_56 = lean_string_dec_eq(x_53, x_55);
lean_dec(x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_57 = lean_apply_1(x_6, x_1);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_58 = x_1;
} else {
 lean_dec_ref(x_1);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
x_60 = lean_string_dec_eq(x_13, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_4);
x_61 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
x_62 = lean_string_dec_eq(x_13, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
x_63 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_63, 0, x_9);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set_usize(x_63, 2, x_54);
lean_ctor_set(x_7, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(4, 2, 8);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_7);
lean_ctor_set(x_64, 1, x_10);
lean_ctor_set_uint64(x_64, sizeof(void*)*2, x_12);
x_65 = lean_apply_1(x_6, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_58);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_6);
x_66 = lean_box_uint64(x_12);
x_67 = lean_box_usize(x_54);
x_68 = lean_box_usize(x_14);
x_69 = lean_apply_4(x_5, x_10, x_66, x_67, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_58);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_70 = lean_box_uint64(x_12);
x_71 = lean_box_usize(x_54);
x_72 = lean_box_usize(x_14);
x_73 = lean_apply_4(x_4, x_10, x_70, x_71, x_72);
return x_73;
}
}
}
}
else
{
uint64_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_75 = lean_ctor_get(x_7, 1);
x_76 = lean_ctor_get_usize(x_7, 2);
lean_inc(x_75);
lean_dec(x_7);
x_77 = lean_ctor_get(x_8, 1);
lean_inc(x_77);
x_78 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_79 = x_8;
} else {
 lean_dec_ref(x_8);
 x_79 = lean_box(0);
}
x_80 = l_Lean_mkAppStx___closed__1;
x_81 = lean_string_dec_eq(x_77, x_80);
lean_dec(x_77);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_apply_1(x_6, x_1);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_83 = x_1;
} else {
 lean_dec_ref(x_1);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
x_85 = lean_string_dec_eq(x_75, x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
lean_dec(x_4);
x_86 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
x_87 = lean_string_dec_eq(x_75, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_5);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_9);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set_usize(x_88, 2, x_78);
x_89 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
lean_ctor_set_usize(x_89, 2, x_76);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(4, 2, 8);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_10);
lean_ctor_set_uint64(x_90, sizeof(void*)*2, x_74);
x_91 = lean_apply_1(x_6, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_6);
x_92 = lean_box_uint64(x_74);
x_93 = lean_box_usize(x_78);
x_94 = lean_box_usize(x_76);
x_95 = lean_apply_4(x_5, x_10, x_92, x_93, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_5);
x_96 = lean_box_uint64(x_74);
x_97 = lean_box_usize(x_78);
x_98 = lean_box_usize(x_76);
x_99 = lean_apply_4(x_4, x_10, x_96, x_97, x_98);
return x_99;
}
}
}
}
case 1:
{
lean_object* x_100; 
lean_dec(x_5);
lean_dec(x_4);
x_100 = lean_ctor_get(x_9, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
x_102 = !lean_is_exclusive(x_7);
if (x_102 == 0)
{
uint64_t x_103; lean_object* x_104; size_t x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_104 = lean_ctor_get(x_7, 1);
x_105 = lean_ctor_get_usize(x_7, 2);
x_106 = lean_ctor_get(x_7, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
lean_object* x_108; size_t x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_8, 1);
x_109 = lean_ctor_get_usize(x_8, 2);
x_110 = lean_ctor_get(x_8, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_9);
if (x_111 == 0)
{
lean_object* x_112; size_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_9, 1);
x_113 = lean_ctor_get_usize(x_9, 2);
x_114 = lean_ctor_get(x_9, 0);
lean_dec(x_114);
x_115 = l_Lean_mkAppStx___closed__1;
x_116 = lean_string_dec_eq(x_112, x_115);
lean_dec(x_112);
if (x_116 == 0)
{
lean_object* x_117; 
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_108);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_apply_1(x_6, x_1);
return x_117;
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_1);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_1, 1);
lean_dec(x_119);
x_120 = lean_ctor_get(x_1, 0);
lean_dec(x_120);
x_121 = l_Lean_mkAppStx___closed__3;
x_122 = lean_string_dec_eq(x_108, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 1, x_115);
x_123 = lean_apply_1(x_6, x_1);
return x_123;
}
else
{
lean_object* x_124; uint8_t x_125; 
lean_dec(x_108);
x_124 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_125 = lean_string_dec_eq(x_104, x_124);
if (x_125 == 0)
{
uint8_t x_126; 
lean_dec(x_2);
x_126 = lean_string_dec_eq(x_104, x_121);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_3);
lean_ctor_set(x_9, 1, x_115);
lean_ctor_set(x_8, 1, x_121);
x_127 = lean_apply_1(x_6, x_1);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_1);
lean_free_object(x_9);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
x_128 = lean_box_uint64(x_103);
x_129 = lean_box_usize(x_113);
x_130 = lean_box_usize(x_109);
x_131 = lean_box_usize(x_105);
x_132 = lean_apply_5(x_3, x_101, x_128, x_129, x_130, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_free_object(x_1);
lean_free_object(x_9);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_3);
x_133 = lean_box_uint64(x_103);
x_134 = lean_box_usize(x_113);
x_135 = lean_box_usize(x_109);
x_136 = lean_box_usize(x_105);
x_137 = lean_apply_5(x_2, x_101, x_133, x_134, x_135, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; uint8_t x_139; 
lean_dec(x_1);
x_138 = l_Lean_mkAppStx___closed__3;
x_139 = lean_string_dec_eq(x_108, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 1, x_115);
x_140 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_140, 0, x_7);
lean_ctor_set(x_140, 1, x_101);
lean_ctor_set_uint64(x_140, sizeof(void*)*2, x_103);
x_141 = lean_apply_1(x_6, x_140);
return x_141;
}
else
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_108);
x_142 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_143 = lean_string_dec_eq(x_104, x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_2);
x_144 = lean_string_dec_eq(x_104, x_138);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_3);
lean_ctor_set(x_9, 1, x_115);
lean_ctor_set(x_8, 1, x_138);
x_145 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_145, 0, x_7);
lean_ctor_set(x_145, 1, x_101);
lean_ctor_set_uint64(x_145, sizeof(void*)*2, x_103);
x_146 = lean_apply_1(x_6, x_145);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_free_object(x_9);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
x_147 = lean_box_uint64(x_103);
x_148 = lean_box_usize(x_113);
x_149 = lean_box_usize(x_109);
x_150 = lean_box_usize(x_105);
x_151 = lean_apply_5(x_3, x_101, x_147, x_148, x_149, x_150);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_free_object(x_9);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_3);
x_152 = lean_box_uint64(x_103);
x_153 = lean_box_usize(x_113);
x_154 = lean_box_usize(x_109);
x_155 = lean_box_usize(x_105);
x_156 = lean_apply_5(x_2, x_101, x_152, x_153, x_154, x_155);
return x_156;
}
}
}
}
}
else
{
lean_object* x_157; size_t x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_9, 1);
x_158 = lean_ctor_get_usize(x_9, 2);
lean_inc(x_157);
lean_dec(x_9);
x_159 = l_Lean_mkAppStx___closed__1;
x_160 = lean_string_dec_eq(x_157, x_159);
lean_dec(x_157);
if (x_160 == 0)
{
lean_object* x_161; 
lean_free_object(x_8);
lean_dec(x_108);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_apply_1(x_6, x_1);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_162 = x_1;
} else {
 lean_dec_ref(x_1);
 x_162 = lean_box(0);
}
x_163 = l_Lean_mkAppStx___closed__3;
x_164 = lean_string_dec_eq(x_108, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_3);
lean_dec(x_2);
x_165 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_165, 0, x_100);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set_usize(x_165, 2, x_158);
lean_ctor_set(x_8, 0, x_165);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(4, 2, 8);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_7);
lean_ctor_set(x_166, 1, x_101);
lean_ctor_set_uint64(x_166, sizeof(void*)*2, x_103);
x_167 = lean_apply_1(x_6, x_166);
return x_167;
}
else
{
lean_object* x_168; uint8_t x_169; 
lean_dec(x_108);
x_168 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_169 = lean_string_dec_eq(x_104, x_168);
if (x_169 == 0)
{
uint8_t x_170; 
lean_dec(x_2);
x_170 = lean_string_dec_eq(x_104, x_163);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_3);
x_171 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_171, 0, x_100);
lean_ctor_set(x_171, 1, x_159);
lean_ctor_set_usize(x_171, 2, x_158);
lean_ctor_set(x_8, 1, x_163);
lean_ctor_set(x_8, 0, x_171);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(4, 2, 8);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_7);
lean_ctor_set(x_172, 1, x_101);
lean_ctor_set_uint64(x_172, sizeof(void*)*2, x_103);
x_173 = lean_apply_1(x_6, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_162);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
x_174 = lean_box_uint64(x_103);
x_175 = lean_box_usize(x_158);
x_176 = lean_box_usize(x_109);
x_177 = lean_box_usize(x_105);
x_178 = lean_apply_5(x_3, x_101, x_174, x_175, x_176, x_177);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_162);
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_3);
x_179 = lean_box_uint64(x_103);
x_180 = lean_box_usize(x_158);
x_181 = lean_box_usize(x_109);
x_182 = lean_box_usize(x_105);
x_183 = lean_apply_5(x_2, x_101, x_179, x_180, x_181, x_182);
return x_183;
}
}
}
}
}
else
{
lean_object* x_184; size_t x_185; lean_object* x_186; size_t x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_184 = lean_ctor_get(x_8, 1);
x_185 = lean_ctor_get_usize(x_8, 2);
lean_inc(x_184);
lean_dec(x_8);
x_186 = lean_ctor_get(x_9, 1);
lean_inc(x_186);
x_187 = lean_ctor_get_usize(x_9, 2);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_188 = x_9;
} else {
 lean_dec_ref(x_9);
 x_188 = lean_box(0);
}
x_189 = l_Lean_mkAppStx___closed__1;
x_190 = lean_string_dec_eq(x_186, x_189);
lean_dec(x_186);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_184);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_apply_1(x_6, x_1);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_192 = x_1;
} else {
 lean_dec_ref(x_1);
 x_192 = lean_box(0);
}
x_193 = l_Lean_mkAppStx___closed__3;
x_194 = lean_string_dec_eq(x_184, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_188)) {
 x_195 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_195 = x_188;
}
lean_ctor_set(x_195, 0, x_100);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set_usize(x_195, 2, x_187);
x_196 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_184);
lean_ctor_set_usize(x_196, 2, x_185);
lean_ctor_set(x_7, 0, x_196);
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(4, 2, 8);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_7);
lean_ctor_set(x_197, 1, x_101);
lean_ctor_set_uint64(x_197, sizeof(void*)*2, x_103);
x_198 = lean_apply_1(x_6, x_197);
return x_198;
}
else
{
lean_object* x_199; uint8_t x_200; 
lean_dec(x_184);
x_199 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_200 = lean_string_dec_eq(x_104, x_199);
if (x_200 == 0)
{
uint8_t x_201; 
lean_dec(x_2);
x_201 = lean_string_dec_eq(x_104, x_193);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_3);
if (lean_is_scalar(x_188)) {
 x_202 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_202 = x_188;
}
lean_ctor_set(x_202, 0, x_100);
lean_ctor_set(x_202, 1, x_189);
lean_ctor_set_usize(x_202, 2, x_187);
x_203 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_193);
lean_ctor_set_usize(x_203, 2, x_185);
lean_ctor_set(x_7, 0, x_203);
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(4, 2, 8);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_7);
lean_ctor_set(x_204, 1, x_101);
lean_ctor_set_uint64(x_204, sizeof(void*)*2, x_103);
x_205 = lean_apply_1(x_6, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_192);
lean_dec(x_188);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
x_206 = lean_box_uint64(x_103);
x_207 = lean_box_usize(x_187);
x_208 = lean_box_usize(x_185);
x_209 = lean_box_usize(x_105);
x_210 = lean_apply_5(x_3, x_101, x_206, x_207, x_208, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_192);
lean_dec(x_188);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_3);
x_211 = lean_box_uint64(x_103);
x_212 = lean_box_usize(x_187);
x_213 = lean_box_usize(x_185);
x_214 = lean_box_usize(x_105);
x_215 = lean_apply_5(x_2, x_101, x_211, x_212, x_213, x_214);
return x_215;
}
}
}
}
}
else
{
uint64_t x_216; lean_object* x_217; size_t x_218; lean_object* x_219; size_t x_220; lean_object* x_221; lean_object* x_222; size_t x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_216 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_217 = lean_ctor_get(x_7, 1);
x_218 = lean_ctor_get_usize(x_7, 2);
lean_inc(x_217);
lean_dec(x_7);
x_219 = lean_ctor_get(x_8, 1);
lean_inc(x_219);
x_220 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_221 = x_8;
} else {
 lean_dec_ref(x_8);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_9, 1);
lean_inc(x_222);
x_223 = lean_ctor_get_usize(x_9, 2);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_224 = x_9;
} else {
 lean_dec_ref(x_9);
 x_224 = lean_box(0);
}
x_225 = l_Lean_mkAppStx___closed__1;
x_226 = lean_string_dec_eq(x_222, x_225);
lean_dec(x_222);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_2);
x_227 = lean_apply_1(x_6, x_1);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_228 = x_1;
} else {
 lean_dec_ref(x_1);
 x_228 = lean_box(0);
}
x_229 = l_Lean_mkAppStx___closed__3;
x_230 = lean_string_dec_eq(x_219, x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_224)) {
 x_231 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_231 = x_224;
}
lean_ctor_set(x_231, 0, x_100);
lean_ctor_set(x_231, 1, x_225);
lean_ctor_set_usize(x_231, 2, x_223);
if (lean_is_scalar(x_221)) {
 x_232 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_232 = x_221;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_219);
lean_ctor_set_usize(x_232, 2, x_220);
x_233 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_217);
lean_ctor_set_usize(x_233, 2, x_218);
if (lean_is_scalar(x_228)) {
 x_234 = lean_alloc_ctor(4, 2, 8);
} else {
 x_234 = x_228;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_101);
lean_ctor_set_uint64(x_234, sizeof(void*)*2, x_216);
x_235 = lean_apply_1(x_6, x_234);
return x_235;
}
else
{
lean_object* x_236; uint8_t x_237; 
lean_dec(x_219);
x_236 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_237 = lean_string_dec_eq(x_217, x_236);
if (x_237 == 0)
{
uint8_t x_238; 
lean_dec(x_2);
x_238 = lean_string_dec_eq(x_217, x_229);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_3);
if (lean_is_scalar(x_224)) {
 x_239 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_239 = x_224;
}
lean_ctor_set(x_239, 0, x_100);
lean_ctor_set(x_239, 1, x_225);
lean_ctor_set_usize(x_239, 2, x_223);
if (lean_is_scalar(x_221)) {
 x_240 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_240 = x_221;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_229);
lean_ctor_set_usize(x_240, 2, x_220);
x_241 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_217);
lean_ctor_set_usize(x_241, 2, x_218);
if (lean_is_scalar(x_228)) {
 x_242 = lean_alloc_ctor(4, 2, 8);
} else {
 x_242 = x_228;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_101);
lean_ctor_set_uint64(x_242, sizeof(void*)*2, x_216);
x_243 = lean_apply_1(x_6, x_242);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_228);
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_217);
lean_dec(x_6);
x_244 = lean_box_uint64(x_216);
x_245 = lean_box_usize(x_223);
x_246 = lean_box_usize(x_220);
x_247 = lean_box_usize(x_218);
x_248 = lean_apply_5(x_3, x_101, x_244, x_245, x_246, x_247);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_228);
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_3);
x_249 = lean_box_uint64(x_216);
x_250 = lean_box_usize(x_223);
x_251 = lean_box_usize(x_220);
x_252 = lean_box_usize(x_218);
x_253 = lean_apply_5(x_2, x_101, x_249, x_250, x_251, x_252);
return x_253;
}
}
}
}
}
else
{
lean_object* x_254; 
lean_dec(x_100);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_apply_1(x_6, x_1);
return x_254;
}
}
default: 
{
lean_object* x_255; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_255 = lean_apply_1(x_6, x_1);
return x_255;
}
}
}
else
{
lean_object* x_256; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_256 = lean_apply_1(x_6, x_1);
return x_256;
}
}
else
{
lean_object* x_257; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_257 = lean_apply_1(x_6, x_1);
return x_257;
}
}
else
{
lean_object* x_258; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_258 = lean_apply_1(x_6, x_1);
return x_258;
}
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstantUnsafe_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parser type at '");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected");
return x_1;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_4);
x_9 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lean_ConstantInfo_type(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_mkAppStx___closed__1;
x_22 = lean_string_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_1);
x_23 = l_System_FilePath_dirName___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_4);
x_25 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1;
x_31 = lean_string_dec_eq(x_19, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2;
x_33 = lean_string_dec_eq(x_19, x_32);
lean_dec(x_19);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
lean_dec(x_1);
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_4);
x_36 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = lean_eval_const(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_apply_1(x_5, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_46, 0, x_54);
return x_46;
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_19);
x_60 = lean_eval_const(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_apply_1(x_5, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_65, 0, x_73);
return x_65;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_65, 0);
lean_inc(x_74);
lean_dec(x_65);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
}
case 1:
{
lean_object* x_79; 
lean_dec(x_5);
x_79 = lean_ctor_get(x_18, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_dec(x_16);
x_81 = lean_ctor_get(x_17, 1);
lean_inc(x_81);
lean_dec(x_17);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
lean_dec(x_18);
x_83 = l_Lean_mkAppStx___closed__1;
x_84 = lean_string_dec_eq(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_1);
x_85 = l_System_FilePath_dirName___closed__1;
x_86 = l_Lean_Name_toStringWithSep___main(x_85, x_4);
x_87 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_mkAppStx___closed__3;
x_93 = lean_string_dec_eq(x_81, x_92);
lean_dec(x_81);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_80);
lean_dec(x_1);
x_94 = l_System_FilePath_dirName___closed__1;
x_95 = l_Lean_Name_toStringWithSep___main(x_94, x_4);
x_96 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_97 = lean_string_append(x_96, x_95);
lean_dec(x_95);
x_98 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_102 = lean_string_dec_eq(x_80, x_101);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = lean_string_dec_eq(x_80, x_92);
lean_dec(x_80);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_104 = l_System_FilePath_dirName___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_4);
x_106 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_108 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
else
{
lean_object* x_111; 
x_111 = lean_eval_const(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_111, 0);
x_117 = 1;
x_118 = lean_box(x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_111, 0, x_119);
return x_111;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
lean_dec(x_111);
x_121 = 1;
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_80);
x_125 = lean_eval_const(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = 0;
x_132 = lean_box(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_125, 0, x_133);
return x_125;
}
else
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_125, 0);
lean_inc(x_134);
lean_dec(x_125);
x_135 = 0;
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_79);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_139 = l_System_FilePath_dirName___closed__1;
x_140 = l_Lean_Name_toStringWithSep___main(x_139, x_4);
x_141 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_1);
x_146 = l_System_FilePath_dirName___closed__1;
x_147 = l_Lean_Name_toStringWithSep___main(x_146, x_4);
x_148 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_149 = lean_string_append(x_148, x_147);
lean_dec(x_147);
x_150 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_151 = lean_string_append(x_149, x_150);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_1);
x_153 = l_System_FilePath_dirName___closed__1;
x_154 = l_Lean_Name_toStringWithSep___main(x_153, x_4);
x_155 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_156 = lean_string_append(x_155, x_154);
lean_dec(x_154);
x_157 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_1);
x_160 = l_System_FilePath_dirName___closed__1;
x_161 = l_Lean_Name_toStringWithSep___main(x_160, x_4);
x_162 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_163 = lean_string_append(x_162, x_161);
lean_dec(x_161);
x_164 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_165 = lean_string_append(x_163, x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_167 = l_System_FilePath_dirName___closed__1;
x_168 = l_Lean_Name_toStringWithSep___main(x_167, x_4);
x_169 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_170 = lean_string_append(x_169, x_168);
lean_dec(x_168);
x_171 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkParserOfConstantUnsafe(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAttributeImplOfConstant___closed__1;
return x_6;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkParserOfConstantAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_compileParserDescr_visit_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_compileParserDescr_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_compileParserDescr_visit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_compileParserDescr_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_compileParserDescr_visit_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_apply_2(x_2, x_25, x_26);
return x_27;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_2(x_3, x_28, x_29);
return x_30;
}
case 2:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_1(x_4, x_31);
return x_32;
}
case 3:
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_apply_1(x_5, x_33);
return x_34;
}
case 4:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_apply_1(x_6, x_35);
return x_36;
}
case 5:
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_apply_1(x_8, x_37);
return x_38;
}
case 6:
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_apply_1(x_9, x_39);
return x_40;
}
case 7:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_apply_2(x_10, x_41, x_42);
return x_43;
}
case 8:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_apply_2(x_11, x_44, x_45);
return x_46;
}
case 9:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_apply_3(x_12, x_47, x_48, x_49);
return x_50;
}
case 10:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_apply_3(x_13, x_51, x_52, x_53);
return x_54;
}
case 11:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_apply_1(x_14, x_55);
return x_56;
}
case 12:
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_59 = lean_box(x_58);
x_60 = lean_apply_2(x_22, x_57, x_59);
return x_60;
}
case 13:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_apply_1(x_15, x_61);
return x_62;
}
case 14:
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = lean_apply_1(x_16, x_63);
return x_64;
}
case 15:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_box(0);
x_66 = lean_apply_1(x_17, x_65);
return x_66;
}
case 16:
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_apply_1(x_18, x_67);
return x_68;
}
case 17:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_apply_1(x_19, x_69);
return x_70;
}
case 18:
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
lean_dec(x_1);
x_72 = lean_apply_1(x_20, x_71);
return x_72;
}
case 19:
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
x_74 = lean_apply_1(x_21, x_73);
return x_74;
}
case 20:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_apply_2(x_24, x_75, x_76);
return x_77;
}
case 21:
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_apply_1(x_23, x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_apply_1(x_7, x_80);
return x_81;
}
}
}
}
lean_object* l_Lean_Parser_compileParserDescr_visit_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit_match__3___rarg___boxed), 24, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_compileParserDescr_visit_match__3___rarg___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
_start:
{
lean_object* x_25; 
x_25 = l_Lean_Parser_compileParserDescr_visit_match__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no space");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_compileParserDescr_visit___closed__1;
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_compileParserDescr_visit___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_numLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_compileParserDescr_visit___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("element");
return x_1;
}
}
lean_object* l_Lean_Parser_compileParserDescr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Lean_Parser_andthenInfo(x_18, x_19);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = l_Lean_Parser_andthenInfo(x_26, x_27);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_34);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_35);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = l_Lean_Parser_orelseInfo(x_47, x_48);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_41, 0, x_53);
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = lean_ctor_get(x_40, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = l_Lean_Parser_orelseInfo(x_55, x_56);
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_60, 0, x_58);
lean_closure_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
case 2:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_4, 0);
lean_inc(x_63);
lean_dec(x_4);
x_64 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = l_Lean_Parser_optionaInfo(x_70);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_64, 0, x_74);
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = l_Lean_Parser_optionaInfo(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
case 3:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
lean_dec(x_4);
x_83 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 1);
x_91 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_91, 0, x_90);
lean_ctor_set(x_88, 1, x_91);
return x_83;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_83, 0, x_95);
return x_83;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
lean_dec(x_83);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_100, 0, x_98);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
case 4:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_4, 0);
lean_inc(x_103);
lean_dec(x_4);
x_104 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 1);
x_112 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn), 3, 1);
lean_closure_set(x_112, 0, x_111);
lean_ctor_set(x_109, 1, x_112);
return x_104;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn), 3, 1);
lean_closure_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_104, 0, x_116);
return x_104;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_104, 0);
lean_inc(x_117);
lean_dec(x_104);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn), 3, 1);
lean_closure_set(x_121, 0, x_119);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
case 5:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_4, 0);
lean_inc(x_124);
lean_dec(x_4);
x_125 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = l_Lean_Parser_noFirstTokenInfo(x_131);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_125, 0, x_135);
return x_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_136 = lean_ctor_get(x_125, 0);
lean_inc(x_136);
lean_dec(x_125);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = l_Lean_Parser_noFirstTokenInfo(x_137);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
case 6:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_4, 0);
lean_inc(x_143);
lean_dec(x_4);
x_144 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_143);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_144, 0);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_149, 1);
x_152 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_152, 0, x_151);
lean_ctor_set(x_149, 1, x_152);
return x_144;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_149);
x_155 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_144, 0, x_156);
return x_144;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_157);
lean_dec(x_144);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_161, 0, x_159);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
case 7:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_4, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_4, 1);
lean_inc(x_165);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_166 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_164);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
lean_dec(x_165);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
return x_166;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
lean_dec(x_166);
x_171 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_165);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
lean_dec(x_170);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
return x_171;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_171);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_171, 0);
x_177 = lean_ctor_get(x_170, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
x_179 = l_Lean_Parser_sepByInfo(x_177, x_178);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
lean_dec(x_170);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
x_182 = 0;
x_183 = lean_box(x_182);
x_184 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(x_184, 0, x_183);
lean_closure_set(x_184, 1, x_180);
lean_closure_set(x_184, 2, x_181);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_179);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_171, 0, x_185);
return x_171;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_ctor_get(x_171, 0);
lean_inc(x_186);
lean_dec(x_171);
x_187 = lean_ctor_get(x_170, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = l_Lean_Parser_sepByInfo(x_187, x_188);
x_190 = lean_ctor_get(x_170, 1);
lean_inc(x_190);
lean_dec(x_170);
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_dec(x_186);
x_192 = 0;
x_193 = lean_box(x_192);
x_194 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(x_194, 0, x_193);
lean_closure_set(x_194, 1, x_190);
lean_closure_set(x_194, 2, x_191);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
}
}
}
case 8:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_4, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_4, 1);
lean_inc(x_198);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_199 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_197);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
lean_dec(x_198);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
lean_dec(x_199);
x_204 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_198);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
lean_dec(x_203);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_204);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_209 = lean_ctor_get(x_204, 0);
x_210 = lean_ctor_get(x_203, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = l_Lean_Parser_sepBy1Info(x_210, x_211);
x_213 = lean_ctor_get(x_203, 1);
lean_inc(x_213);
lean_dec(x_203);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
lean_dec(x_209);
x_215 = 0;
x_216 = lean_box(x_215);
x_217 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(x_217, 0, x_216);
lean_closure_set(x_217, 1, x_213);
lean_closure_set(x_217, 2, x_214);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_204, 0, x_218);
return x_204;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_219 = lean_ctor_get(x_204, 0);
lean_inc(x_219);
lean_dec(x_204);
x_220 = lean_ctor_get(x_203, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = l_Lean_Parser_sepBy1Info(x_220, x_221);
x_223 = lean_ctor_get(x_203, 1);
lean_inc(x_223);
lean_dec(x_203);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
lean_dec(x_219);
x_225 = 0;
x_226 = lean_box(x_225);
x_227 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(x_227, 0, x_226);
lean_closure_set(x_227, 1, x_223);
lean_closure_set(x_227, 2, x_224);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_222);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
}
}
case 9:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_4, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_4, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_4, 2);
lean_inc(x_232);
lean_dec(x_4);
x_233 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_232);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
lean_dec(x_231);
lean_dec(x_230);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
return x_233;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
}
else
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_233);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_238 = lean_ctor_get(x_233, 0);
x_239 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_239, 0, x_231);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
lean_inc(x_230);
x_241 = l_Lean_Parser_nodeInfo(x_230, x_240);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_243, 0, x_230);
lean_closure_set(x_243, 1, x_242);
x_244 = l_Lean_Parser_epsilonInfo;
x_245 = l_Lean_Parser_andthenInfo(x_244, x_241);
x_246 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_246, 0, x_239);
lean_closure_set(x_246, 1, x_243);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set(x_233, 0, x_247);
return x_233;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_248 = lean_ctor_get(x_233, 0);
lean_inc(x_248);
lean_dec(x_233);
x_249 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_249, 0, x_231);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_inc(x_230);
x_251 = l_Lean_Parser_nodeInfo(x_230, x_250);
x_252 = lean_ctor_get(x_248, 1);
lean_inc(x_252);
lean_dec(x_248);
x_253 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_253, 0, x_230);
lean_closure_set(x_253, 1, x_252);
x_254 = l_Lean_Parser_epsilonInfo;
x_255 = l_Lean_Parser_andthenInfo(x_254, x_251);
x_256 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_256, 0, x_249);
lean_closure_set(x_256, 1, x_253);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
case 10:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_4, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_4, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_4, 2);
lean_inc(x_261);
lean_dec(x_4);
x_262 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_261);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
lean_dec(x_260);
lean_dec(x_259);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
return x_262;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
return x_265;
}
}
else
{
uint8_t x_266; 
x_266 = !lean_is_exclusive(x_262);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_267 = lean_ctor_get(x_262, 0);
x_268 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_268, 0, x_260);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
lean_inc(x_259);
x_270 = l_Lean_Parser_nodeInfo(x_259, x_269);
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_dec(x_267);
x_272 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_272, 0, x_259);
lean_closure_set(x_272, 1, x_271);
x_273 = l_Lean_Parser_epsilonInfo;
x_274 = l_Lean_Parser_andthenInfo(x_273, x_270);
x_275 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_275, 0, x_268);
lean_closure_set(x_275, 1, x_272);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
lean_ctor_set(x_262, 0, x_276);
return x_262;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_277 = lean_ctor_get(x_262, 0);
lean_inc(x_277);
lean_dec(x_262);
x_278 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_278, 0, x_260);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_inc(x_259);
x_280 = l_Lean_Parser_nodeInfo(x_259, x_279);
x_281 = lean_ctor_get(x_277, 1);
lean_inc(x_281);
lean_dec(x_277);
x_282 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_282, 0, x_259);
lean_closure_set(x_282, 1, x_281);
x_283 = l_Lean_Parser_epsilonInfo;
x_284 = l_Lean_Parser_andthenInfo(x_283, x_280);
x_285 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_285, 0, x_278);
lean_closure_set(x_285, 1, x_282);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
}
}
case 11:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_288 = lean_ctor_get(x_4, 0);
lean_inc(x_288);
lean_dec(x_4);
x_289 = l_String_trim(x_288);
lean_dec(x_288);
lean_inc(x_289);
x_290 = l_Lean_Parser_symbolInfo(x_289);
x_291 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_291, 0, x_289);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
case 12:
{
lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_ctor_get(x_4, 0);
lean_inc(x_294);
x_295 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_296 = l_String_trim(x_294);
lean_dec(x_294);
lean_inc(x_296);
x_297 = l_Lean_Parser_nonReservedSymbolInfo(x_296, x_295);
x_298 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_298, 0, x_296);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
case 13:
{
lean_object* x_301; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = l_Lean_Parser_compileParserDescr_visit___closed__3;
return x_301;
}
case 14:
{
lean_object* x_302; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = l_Lean_Parser_compileParserDescr_visit___closed__4;
return x_302;
}
case 15:
{
lean_object* x_303; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_303 = l_Lean_Parser_compileParserDescr_visit___closed__5;
return x_303;
}
case 16:
{
lean_object* x_304; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = l_Lean_Parser_compileParserDescr_visit___closed__6;
return x_304;
}
case 17:
{
lean_object* x_305; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = l_Lean_Parser_compileParserDescr_visit___closed__7;
return x_305;
}
case 18:
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_4, 0);
lean_inc(x_306);
lean_dec(x_4);
x_307 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_306);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
return x_307;
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_309);
return x_310;
}
}
else
{
uint8_t x_311; 
x_311 = !lean_is_exclusive(x_307);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_307, 0);
x_313 = l_Lean_Parser_interpolatedStr(x_312);
lean_ctor_set(x_307, 0, x_313);
return x_307;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_307, 0);
lean_inc(x_314);
lean_dec(x_307);
x_315 = l_Lean_Parser_interpolatedStr(x_314);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
return x_316;
}
}
}
case 19:
{
lean_object* x_317; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_317 = l_Lean_Parser_compileParserDescr_visit___closed__8;
return x_317;
}
case 20:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_2);
lean_dec(x_1);
x_318 = lean_ctor_get(x_4, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_4, 1);
lean_inc(x_319);
lean_dec(x_4);
x_320 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_3, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; 
lean_dec(x_319);
x_321 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_318);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_320);
x_322 = l_Lean_Parser_categoryParser(x_318, x_319);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
return x_323;
}
}
case 21:
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_4, 0);
lean_inc(x_324);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_325 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit), 4, 3);
lean_closure_set(x_325, 0, x_1);
lean_closure_set(x_325, 1, x_2);
lean_closure_set(x_325, 2, x_3);
x_326 = l_Lean_Parser_mkParserOfConstantUnsafe(x_1, x_2, x_3, x_324, x_325);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_326) == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
return x_326;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
}
else
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_326);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_326, 0);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
lean_ctor_set(x_326, 0, x_332);
return x_326;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_326, 0);
lean_inc(x_333);
lean_dec(x_326);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
}
}
default: 
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_4, 0);
lean_inc(x_336);
lean_dec(x_4);
x_337 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_336);
if (lean_obj_tag(x_337) == 0)
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_337);
if (x_338 == 0)
{
return x_337;
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_340, 0, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_337);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_342 = lean_ctor_get(x_337, 0);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_344 = l_Lean_Parser_compileParserDescr_visit___closed__9;
x_345 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_345, 0, x_343);
lean_closure_set(x_345, 1, x_344);
x_346 = l_Lean_Parser_Lean_Parser_Basic___instance__8___closed__1;
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_345);
lean_ctor_set(x_337, 0, x_347);
return x_337;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_348 = lean_ctor_get(x_337, 0);
lean_inc(x_348);
lean_dec(x_337);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_350 = l_Lean_Parser_compileParserDescr_visit___closed__9;
x_351 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_351, 0, x_349);
lean_closure_set(x_351, 1, x_350);
x_352 = l_Lean_Parser_Lean_Parser_Basic___instance__8___closed__1;
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
}
}
}
}
}
lean_object* l_Lean_Parser_compileParserDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = l_Lean_Parser_mkParserOfConstantUnsafe(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_IO_mkRef___at_Lean_Parser_mkParserAttributeHooks___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_mkParserAttributeHooks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___at_Lean_Parser_mkParserAttributeHooks___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_Lean_Parser_parserAttributeHooks;
x_4 = lean_st_ref_take(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_st_ref_set(x_3, x_7, x_6);
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
lean_object* l_List_forM___main___at_Lean_Parser_runParserAttributeHooks___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_apply_7(x_11, x_1, x_2, x_13, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_4 = x_12;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Parser_parserAttributeHooks;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_forM___main___at_Lean_Parser_runParserAttributeHooks___spec__1(x_1, x_2, x_3, x_10, x_4, x_5, x_6, x_11);
return x_12;
}
}
lean_object* l_List_forM___main___at_Lean_Parser_runParserAttributeHooks___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_List_forM___main___at_Lean_Parser_runParserAttributeHooks___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lean_ToExpr___instance__7___closed__1;
x_2 = l___private_Init_LeanInit_13__quoteName___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1;
x_8 = 1;
x_9 = l_Lean_Parser_runParserAttributeHooks(x_7, x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'runBuiltinParserAttributeHooks', unexpected argument");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_hasArgs(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1(x_1, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_11 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__3;
x_12 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_11, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runBuiltinParserAttributeHooks");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitly run hooks normally activated by builtin parser attributes");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__3;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__4;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__6;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1;
x_8 = 0;
x_9 = l_Lean_Parser_runParserAttributeHooks(x_7, x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'runParserAttributeHooks', unexpected argument");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_hasArgs(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__1(x_1, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_11 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__3;
x_12 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_11, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runParserAttributeHooks");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitly run hooks normally activated by parser attributes");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__3;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__4;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__6;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_apply_2(x_4, x_10, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_3(x_5, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
x_20 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_16, x_14);
x_21 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1(x_20, x_7);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_5, 0, x_22);
x_4 = x_13;
x_7 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_free_object(x_5);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_33 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_29, x_14);
x_34 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1(x_33, x_7);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
x_4 = x_13;
x_5 = x_37;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_1);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
case 1:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
lean_dec(x_11);
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_5, 1);
x_46 = lean_box(0);
x_47 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_45, x_43, x_46);
lean_ctor_set(x_5, 1, x_47);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_ctor_get(x_5, 1);
x_51 = lean_ctor_get(x_5, 2);
x_52 = lean_ctor_get(x_5, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_5);
x_53 = lean_box(0);
x_54 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_50, x_43, x_53);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
x_4 = x_13;
x_5 = x_55;
goto _start;
}
}
case 2:
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_59 = !lean_is_exclusive(x_5);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_5, 0);
x_61 = lean_ctor_get(x_5, 1);
x_62 = lean_ctor_get(x_5, 2);
x_63 = lean_ctor_get(x_5, 3);
x_64 = l_Lean_Parser_Lean_Parser_Basic___instance__14___closed__1;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_58);
x_66 = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(x_62, x_57, x_65);
x_67 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_66, x_7);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_ctor_set(x_5, 2, x_68);
x_4 = x_13;
x_7 = x_69;
goto _start;
}
else
{
uint8_t x_71; 
lean_free_object(x_5);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_5, 0);
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_ctor_get(x_5, 2);
x_78 = lean_ctor_get(x_5, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_5);
x_79 = l_Lean_Parser_Lean_Parser_Basic___instance__14___closed__1;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_58);
x_81 = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(x_77, x_57, x_80);
x_82 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_81, x_7);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_78);
x_4 = x_13;
x_5 = x_85;
x_7 = x_84;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_13);
lean_dec(x_1);
x_87 = lean_ctor_get(x_82, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_89 = x_82;
} else {
 lean_dec_ref(x_82);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
default: 
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_11, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_11, 2);
lean_inc(x_93);
lean_dec(x_11);
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
x_96 = !lean_is_exclusive(x_5);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_5, 0);
x_98 = lean_ctor_get(x_5, 1);
x_99 = lean_ctor_get(x_5, 2);
x_100 = lean_ctor_get(x_5, 3);
lean_inc(x_92);
lean_inc(x_99);
x_101 = l_Lean_Parser_mkParserOfConstant(x_94, x_95, x_99, x_92);
x_102 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2(x_101, x_7);
lean_dec(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_unbox(x_105);
lean_dec(x_105);
x_108 = l_Lean_Parser_addParser(x_99, x_91, x_92, x_107, x_106, x_93);
lean_dec(x_92);
x_109 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_108, x_104);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_ctor_set(x_5, 2, x_110);
x_4 = x_13;
x_7 = x_111;
goto _start;
}
else
{
uint8_t x_113; 
lean_free_object(x_5);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_13);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 0);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_109);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_free_object(x_5);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_102);
if (x_117 == 0)
{
return x_102;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_102, 0);
x_119 = lean_ctor_get(x_102, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_102);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_5, 0);
x_122 = lean_ctor_get(x_5, 1);
x_123 = lean_ctor_get(x_5, 2);
x_124 = lean_ctor_get(x_5, 3);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_5);
lean_inc(x_92);
lean_inc(x_123);
x_125 = l_Lean_Parser_mkParserOfConstant(x_94, x_95, x_123, x_92);
x_126 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2(x_125, x_7);
lean_dec(x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_unbox(x_129);
lean_dec(x_129);
x_132 = l_Lean_Parser_addParser(x_123, x_91, x_92, x_131, x_130, x_93);
lean_dec(x_92);
x_133 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_132, x_128);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_122);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_124);
x_4 = x_13;
x_5 = x_136;
x_7 = x_135;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_13);
lean_dec(x_1);
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_1);
x_142 = lean_ctor_get(x_126, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_144 = x_126;
} else {
 lean_dec_ref(x_126);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_15 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__3(x_2, x_11, x_11, x_14, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_4 = x_13;
x_5 = x_16;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__4(x_1, x_2, x_1, x_7, x_5, x_2, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerInternalExceptionId___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2(x_1, x_21, x_21, x_23, x_24);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_26, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_28);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_registerInternalExceptionId___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
}
}
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_List_reverse___rarg(x_2);
x_4 = l_List_redLength___main___rarg(x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l_List_toArrayAux___main___rarg(x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parserExt");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_addImported___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__3;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__4;
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__5;
x_5 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__6;
x_6 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__7;
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
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__8;
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Init_System_IOError___instance__2___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_parserExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserExtension___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Parser_parserExtension___closed__1;
x_4 = l_Lean_Parser_parserExtension___closed__2;
x_5 = l_Lean_Parser_parserExtension___closed__3;
x_6 = l_Lean_Parser_parserExtension___closed__4;
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
lean_object* l_Lean_Parser_parserExtension___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_parserExtension___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_parserExtension___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_parserExtension___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_parserExtension___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_parserExtension___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_Parser_isParserCategory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_Parser_parserExtension;
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_5, x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isParserCategory(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_addParserCategory(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Parser_isParserCategory(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_3);
x_6 = l_Lean_Parser_parserExtension;
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_6, x_1, x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg(x_2);
return x_9;
}
}
}
lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_addParserCategory(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_leadingIdentAsSymbol_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_leadingIdentAsSymbol_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_leadingIdentAsSymbol_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Parser_leadingIdentAsSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_parserExtension;
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_leadingIdentAsSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_leadingIdentAsSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean_box(0);
x_5 = 1;
x_6 = l_Lean_Parser_mkAntiquot(x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_categoryParserFnImpl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_categoryParserFnImpl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFnImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFnImpl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_categoryParserFnImpl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFnImpl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stx");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFnImpl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_categoryParserFnImpl___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_categoryParserFnImpl___closed__2;
x_5 = lean_name_eq(x_1, x_4);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = l_Lean_Parser_parserExtension;
x_8 = l_Lean_PersistentEnvExtension_getState___rarg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
if (x_5 == 0)
{
x_10 = x_1;
goto block_34;
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = l_Lean_Parser_categoryParserFnImpl___closed__4;
x_10 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_11; 
x_11 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_10);
x_14 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec(x_19);
lean_inc(x_10);
x_22 = l_Lean_Parser_mkCategoryAntiquotParser(x_10);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(x_21);
lean_inc(x_20);
lean_inc(x_10);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_20);
lean_closure_set(x_25, 2, x_24);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Parser_tryAnti(x_2, x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_23);
lean_inc(x_2);
lean_inc(x_20);
x_27 = l_Lean_Parser_leadingParserAux(x_10, x_20, x_21, x_2, x_3);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Parser_trailingLoop(x_20, x_2, x_27);
return x_29;
}
else
{
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_2);
return x_27;
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
x_30 = 1;
lean_inc(x_2);
x_31 = l_Lean_Parser_orelseFnCore(x_23, x_25, x_30, x_2, x_3);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Parser_trailingLoop(x_20, x_2, x_31);
return x_33;
}
else
{
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_2);
return x_31;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_setCategoryParserFnRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_setCategoryParserFnRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Parser_categoryParserFnRef;
x_3 = l_Lean_Parser_setCategoryParserFnRef___closed__1;
x_4 = lean_st_ref_set(x_2, x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_addToken(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_parserExtension;
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_2);
x_6 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_parserExtension;
x_5 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_4, x_1, x_3);
return x_5;
}
}
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
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
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_Parser_parserExtension;
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_5, x_2);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isValidSyntaxNodeKind(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_3 = x_9;
x_4 = x_11;
goto _start;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_13, x_4);
lean_dec(x_13);
x_3 = x_9;
x_4 = x_14;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4(x_6, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_parserExtension;
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_getSyntaxNodeKinds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_getSyntaxNodeKinds(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_getTokenTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_parserExtension;
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_getTokenTable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_getTokenTable(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkInputContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = l_Lean_FileMap_ofString(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_mkParserContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_getTokenTable(x_1);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_4);
lean_ctor_set(x_7, 5, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_mkParserState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_runParserCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_5 = l_Lean_Parser_mkInputContext(x_3, x_4);
x_6 = l_Lean_Parser_mkParserContext(x_1, x_5);
x_7 = l_Lean_Parser_mkParserState(x_3);
x_8 = l_Lean_Parser_whitespace(x_6, x_7);
lean_inc(x_6);
x_9 = l_Lean_Parser_categoryParserFnImpl(x_2, x_6, x_8);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_string_utf8_at_end(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_14 = l_Lean_Parser_ParserState_mkError(x_9, x_13);
x_15 = l_Lean_Parser_ParserState_toErrorMsg(x_6, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_3);
x_20 = l_Lean_Parser_ParserState_toErrorMsg(x_6, x_9);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
lean_object* l_Lean_Parser_declareBuiltinParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_declareBuiltinParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_declareBuiltinParser_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_declareBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin parser '");
return x_1;
}
}
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_7 = l_Lean_Parser_declareBuiltinParser___closed__2;
lean_inc(x_4);
x_8 = l_Lean_Name_append___main(x_7, x_4);
x_9 = lean_box(0);
x_10 = l_Lean_mkConst(x_2, x_9);
x_11 = l_Lean_Name_toExprAux(x_3);
lean_inc(x_4);
x_12 = l_Lean_Name_toExprAux(x_4);
lean_inc(x_4);
x_13 = l_Lean_mkConst(x_4, x_9);
x_14 = l_Lean_mkNatLit(x_5);
x_15 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_14);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_19, x_19, x_20, x_10);
lean_dec(x_19);
x_22 = l_Lean_KeyedDeclsAttribute_declareBuiltin___rarg___closed__6;
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_9);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_box(0);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Environment_addAndCompile(x_1, x_9, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_8);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_4);
x_31 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Char_HasRepr___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = l_Lean_regularInitAttr;
x_39 = lean_box(0);
x_40 = l_Lean_ParametricAttribute_setParam___rarg(x_38, x_37, x_8, x_39);
x_41 = l_IO_ofExcept___at_Lean_KeyedDeclsAttribute_declareBuiltin___spec__1(x_40, x_6);
lean_dec(x_40);
return x_41;
}
}
}
static lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinLeadingParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
x_7 = l_Lean_Parser_declareBuiltinParser(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTrailingParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
x_7 = l_Lean_Parser_declareBuiltinParser(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_getParserPriority_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_getParserPriority_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_getParserPriority_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_getParserPriority_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Parser_getParserPriority_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_getParserPriority_match__2___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_getParserPriority___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser attribute, no argument or numeral expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_getParserPriority___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_getParserPriority___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_getParserPriority___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser attribute, numeral expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_getParserPriority___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_getParserPriority___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_getParserPriority___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_getParserPriority(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getNumArgs(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Parser_getParserPriority___closed__2;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Syntax_getArg(x_1, x_3);
lean_dec(x_1);
x_9 = l_Lean_numLitKind;
x_10 = l_Lean_Syntax_isNatLitAux(x_9, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Parser_getParserPriority___closed__4;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Parser_getParserPriority___closed__5;
return x_14;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
uint64_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get_usize(x_5, 2);
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get_usize(x_6, 2);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get_usize(x_7, 2);
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = l_Lean_mkAppStx___closed__1;
x_24 = lean_string_dec_eq(x_20, x_23);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; 
lean_free_object(x_7);
lean_free_object(x_6);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_apply_1(x_4, x_1);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
x_29 = l_Lean_mkAppStx___closed__3;
x_30 = lean_string_dec_eq(x_16, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_7, 1, x_23);
x_31 = lean_apply_1(x_4, x_1);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_16);
x_32 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_33 = lean_string_dec_eq(x_12, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = lean_string_dec_eq(x_12, x_29);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_3);
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_6, 1, x_29);
x_35 = lean_apply_1(x_4, x_1);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_1);
lean_free_object(x_7);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_36 = lean_box_uint64(x_11);
x_37 = lean_box_usize(x_21);
x_38 = lean_box_usize(x_17);
x_39 = lean_box_usize(x_13);
x_40 = lean_apply_5(x_3, x_9, x_36, x_37, x_38, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_1);
lean_free_object(x_7);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_box_uint64(x_11);
x_42 = lean_box_usize(x_21);
x_43 = lean_box_usize(x_17);
x_44 = lean_box_usize(x_13);
x_45 = lean_apply_5(x_2, x_9, x_41, x_42, x_43, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_46 = l_Lean_mkAppStx___closed__3;
x_47 = lean_string_dec_eq(x_16, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_7, 1, x_23);
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_9);
lean_ctor_set_uint64(x_48, sizeof(void*)*2, x_11);
x_49 = lean_apply_1(x_4, x_48);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_16);
x_50 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_51 = lean_string_dec_eq(x_12, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = lean_string_dec_eq(x_12, x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_6, 1, x_46);
x_53 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_9);
lean_ctor_set_uint64(x_53, sizeof(void*)*2, x_11);
x_54 = lean_apply_1(x_4, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_7);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_55 = lean_box_uint64(x_11);
x_56 = lean_box_usize(x_21);
x_57 = lean_box_usize(x_17);
x_58 = lean_box_usize(x_13);
x_59 = lean_apply_5(x_3, x_9, x_55, x_56, x_57, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_7);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_60 = lean_box_uint64(x_11);
x_61 = lean_box_usize(x_21);
x_62 = lean_box_usize(x_17);
x_63 = lean_box_usize(x_13);
x_64 = lean_apply_5(x_2, x_9, x_60, x_61, x_62, x_63);
return x_64;
}
}
}
}
}
else
{
lean_object* x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_7, 1);
x_66 = lean_ctor_get_usize(x_7, 2);
lean_inc(x_65);
lean_dec(x_7);
x_67 = l_Lean_mkAppStx___closed__1;
x_68 = lean_string_dec_eq(x_65, x_67);
lean_dec(x_65);
if (x_68 == 0)
{
lean_object* x_69; 
lean_free_object(x_6);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_apply_1(x_4, x_1);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_70 = x_1;
} else {
 lean_dec_ref(x_1);
 x_70 = lean_box(0);
}
x_71 = l_Lean_mkAppStx___closed__3;
x_72 = lean_string_dec_eq(x_16, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_73, 0, x_8);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set_usize(x_73, 2, x_66);
lean_ctor_set(x_6, 0, x_73);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(4, 2, 8);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_9);
lean_ctor_set_uint64(x_74, sizeof(void*)*2, x_11);
x_75 = lean_apply_1(x_4, x_74);
return x_75;
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_16);
x_76 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_77 = lean_string_dec_eq(x_12, x_76);
if (x_77 == 0)
{
uint8_t x_78; 
lean_dec(x_2);
x_78 = lean_string_dec_eq(x_12, x_71);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
x_79 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_67);
lean_ctor_set_usize(x_79, 2, x_66);
lean_ctor_set(x_6, 1, x_71);
lean_ctor_set(x_6, 0, x_79);
if (lean_is_scalar(x_70)) {
 x_80 = lean_alloc_ctor(4, 2, 8);
} else {
 x_80 = x_70;
}
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_9);
lean_ctor_set_uint64(x_80, sizeof(void*)*2, x_11);
x_81 = lean_apply_1(x_4, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_70);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_82 = lean_box_uint64(x_11);
x_83 = lean_box_usize(x_66);
x_84 = lean_box_usize(x_17);
x_85 = lean_box_usize(x_13);
x_86 = lean_apply_5(x_3, x_9, x_82, x_83, x_84, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_70);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_87 = lean_box_uint64(x_11);
x_88 = lean_box_usize(x_66);
x_89 = lean_box_usize(x_17);
x_90 = lean_box_usize(x_13);
x_91 = lean_apply_5(x_2, x_9, x_87, x_88, x_89, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; size_t x_93; lean_object* x_94; size_t x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_6, 1);
x_93 = lean_ctor_get_usize(x_6, 2);
lean_inc(x_92);
lean_dec(x_6);
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
x_95 = lean_ctor_get_usize(x_7, 2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_96 = x_7;
} else {
 lean_dec_ref(x_7);
 x_96 = lean_box(0);
}
x_97 = l_Lean_mkAppStx___closed__1;
x_98 = lean_string_dec_eq(x_94, x_97);
lean_dec(x_94);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_96);
lean_dec(x_92);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_apply_1(x_4, x_1);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_100 = x_1;
} else {
 lean_dec_ref(x_1);
 x_100 = lean_box(0);
}
x_101 = l_Lean_mkAppStx___closed__3;
x_102 = lean_string_dec_eq(x_92, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_103 = x_96;
}
lean_ctor_set(x_103, 0, x_8);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set_usize(x_103, 2, x_95);
x_104 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_92);
lean_ctor_set_usize(x_104, 2, x_93);
lean_ctor_set(x_5, 0, x_104);
if (lean_is_scalar(x_100)) {
 x_105 = lean_alloc_ctor(4, 2, 8);
} else {
 x_105 = x_100;
}
lean_ctor_set(x_105, 0, x_5);
lean_ctor_set(x_105, 1, x_9);
lean_ctor_set_uint64(x_105, sizeof(void*)*2, x_11);
x_106 = lean_apply_1(x_4, x_105);
return x_106;
}
else
{
lean_object* x_107; uint8_t x_108; 
lean_dec(x_92);
x_107 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_108 = lean_string_dec_eq(x_12, x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_dec(x_2);
x_109 = lean_string_dec_eq(x_12, x_101);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_3);
if (lean_is_scalar(x_96)) {
 x_110 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_110 = x_96;
}
lean_ctor_set(x_110, 0, x_8);
lean_ctor_set(x_110, 1, x_97);
lean_ctor_set_usize(x_110, 2, x_95);
x_111 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_101);
lean_ctor_set_usize(x_111, 2, x_93);
lean_ctor_set(x_5, 0, x_111);
if (lean_is_scalar(x_100)) {
 x_112 = lean_alloc_ctor(4, 2, 8);
} else {
 x_112 = x_100;
}
lean_ctor_set(x_112, 0, x_5);
lean_ctor_set(x_112, 1, x_9);
lean_ctor_set_uint64(x_112, sizeof(void*)*2, x_11);
x_113 = lean_apply_1(x_4, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_100);
lean_dec(x_96);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_114 = lean_box_uint64(x_11);
x_115 = lean_box_usize(x_95);
x_116 = lean_box_usize(x_93);
x_117 = lean_box_usize(x_13);
x_118 = lean_apply_5(x_3, x_9, x_114, x_115, x_116, x_117);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_100);
lean_dec(x_96);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_119 = lean_box_uint64(x_11);
x_120 = lean_box_usize(x_95);
x_121 = lean_box_usize(x_93);
x_122 = lean_box_usize(x_13);
x_123 = lean_apply_5(x_2, x_9, x_119, x_120, x_121, x_122);
return x_123;
}
}
}
}
}
else
{
uint64_t x_124; lean_object* x_125; size_t x_126; lean_object* x_127; size_t x_128; lean_object* x_129; lean_object* x_130; size_t x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_124 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_125 = lean_ctor_get(x_5, 1);
x_126 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_125);
lean_dec(x_5);
x_127 = lean_ctor_get(x_6, 1);
lean_inc(x_127);
x_128 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_129 = x_6;
} else {
 lean_dec_ref(x_6);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_7, 1);
lean_inc(x_130);
x_131 = lean_ctor_get_usize(x_7, 2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_132 = x_7;
} else {
 lean_dec_ref(x_7);
 x_132 = lean_box(0);
}
x_133 = l_Lean_mkAppStx___closed__1;
x_134 = lean_string_dec_eq(x_130, x_133);
lean_dec(x_130);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_apply_1(x_4, x_1);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_136 = x_1;
} else {
 lean_dec_ref(x_1);
 x_136 = lean_box(0);
}
x_137 = l_Lean_mkAppStx___closed__3;
x_138 = lean_string_dec_eq(x_127, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_132)) {
 x_139 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_139 = x_132;
}
lean_ctor_set(x_139, 0, x_8);
lean_ctor_set(x_139, 1, x_133);
lean_ctor_set_usize(x_139, 2, x_131);
if (lean_is_scalar(x_129)) {
 x_140 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_140 = x_129;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_127);
lean_ctor_set_usize(x_140, 2, x_128);
x_141 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_125);
lean_ctor_set_usize(x_141, 2, x_126);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(4, 2, 8);
} else {
 x_142 = x_136;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_9);
lean_ctor_set_uint64(x_142, sizeof(void*)*2, x_124);
x_143 = lean_apply_1(x_4, x_142);
return x_143;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_127);
x_144 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_145 = lean_string_dec_eq(x_125, x_144);
if (x_145 == 0)
{
uint8_t x_146; 
lean_dec(x_2);
x_146 = lean_string_dec_eq(x_125, x_137);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_3);
if (lean_is_scalar(x_132)) {
 x_147 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_147 = x_132;
}
lean_ctor_set(x_147, 0, x_8);
lean_ctor_set(x_147, 1, x_133);
lean_ctor_set_usize(x_147, 2, x_131);
if (lean_is_scalar(x_129)) {
 x_148 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_148 = x_129;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_137);
lean_ctor_set_usize(x_148, 2, x_128);
x_149 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_125);
lean_ctor_set_usize(x_149, 2, x_126);
if (lean_is_scalar(x_136)) {
 x_150 = lean_alloc_ctor(4, 2, 8);
} else {
 x_150 = x_136;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_9);
lean_ctor_set_uint64(x_150, sizeof(void*)*2, x_124);
x_151 = lean_apply_1(x_4, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_4);
x_152 = lean_box_uint64(x_124);
x_153 = lean_box_usize(x_131);
x_154 = lean_box_usize(x_128);
x_155 = lean_box_usize(x_126);
x_156 = lean_apply_5(x_3, x_9, x_152, x_153, x_154, x_155);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_box_uint64(x_124);
x_158 = lean_box_usize(x_131);
x_159 = lean_box_usize(x_128);
x_160 = lean_box_usize(x_126);
x_161 = lean_apply_5(x_2, x_9, x_157, x_158, x_159, x_160);
return x_161;
}
}
}
}
}
else
{
lean_object* x_162; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_162 = lean_apply_1(x_4, x_1);
return x_162;
}
}
else
{
lean_object* x_163; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_163 = lean_apply_1(x_4, x_1);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_164 = lean_apply_1(x_4, x_1);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_165 = lean_apply_1(x_4, x_1);
return x_165;
}
}
else
{
lean_object* x_166; 
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_apply_1(x_4, x_1);
return x_166;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`Parser` or `TrailingParser` expected)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ConstantInfo_type(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_mkAppStx___closed__1;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_30, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_mkAppStx___closed__3;
x_37 = lean_string_dec_eq(x_22, x_36);
lean_dec(x_22);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_39 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_42, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3;
x_49 = lean_string_dec_eq(x_21, x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_string_dec_eq(x_21, x_36);
lean_dec(x_21);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_1);
x_52 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_55, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_6, 3);
lean_inc(x_61);
lean_inc(x_1);
lean_inc(x_2);
x_62 = l_Lean_Parser_declareLeadingBuiltinParser(x_15, x_2, x_1, x_3, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(x_63, x_5, x_6, x_7, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = 1;
x_68 = l_Lean_Parser_runParserAttributeHooks(x_2, x_1, x_67, x_5, x_6, x_7, x_66);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_io_error_to_string(x_70);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_62, 0, x_74);
return x_62;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_62);
x_77 = lean_io_error_to_string(x_75);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_21);
x_82 = lean_ctor_get(x_6, 3);
lean_inc(x_82);
lean_inc(x_1);
lean_inc(x_2);
x_83 = l_Lean_Parser_declareTrailingBuiltinParser(x_15, x_2, x_1, x_3, x_14);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
lean_dec(x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(x_84, x_5, x_6, x_7, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = 1;
x_89 = l_Lean_Parser_runParserAttributeHooks(x_2, x_1, x_88, x_5, x_6, x_7, x_87);
return x_89;
}
else
{
uint8_t x_90; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_83);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_io_error_to_string(x_91);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_82);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_83, 0, x_95);
return x_83;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_83, 0);
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_83);
x_98 = lean_io_error_to_string(x_96);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_82);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_97);
return x_102;
}
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_103, 0, x_1);
x_104 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_107, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
return x_108;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_113, 0, x_1);
x_114 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_117, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_123, 0, x_1);
x_124 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_127, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
return x_128;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_128);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_133, 0, x_1);
x_134 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_137, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
return x_138;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_138);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_143, 0, x_1);
x_144 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_147, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
return x_148;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_148);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_9);
if (x_153 == 0)
{
return x_9;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_9, 0);
x_155 = lean_ctor_get(x_9, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_9);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_getParserPriority(x_4);
x_11 = l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(x_10, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
if (x_5 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_registerTagAttribute___lambda__6___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_17, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(x_3, x_2, x_23, x_25, x_6, x_7, x_8, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin parser");
return x_1;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_8 = 1;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_registerBuiltinAttribute(x_11, x_6);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Parser_registerBuiltinParserAttribute(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser '");
return x_1;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_st_ref_get(x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1;
x_16 = l_Lean_Parser_addToken(x_14, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_1);
x_19 = l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_26, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(x_32, x_3, x_4, x_5, x_13);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = lean_apply_5(x_15, x_34, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_2 = x_10;
x_6 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_st_ref_take(x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = l_Lean_Parser_addSyntaxNodeKind(x_20, x_15);
lean_ctor_set(x_17, 0, x_21);
x_22 = lean_st_ref_set(x_7, x_17, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_3 = x_14;
x_4 = x_24;
x_8 = x_23;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
x_28 = lean_ctor_get(x_17, 2);
x_29 = lean_ctor_get(x_17, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_30 = l_Lean_Parser_addSyntaxNodeKind(x_26, x_15);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = lean_st_ref_set(x_7, x_31, x_18);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_3 = x_14;
x_4 = x_34;
x_8 = x_33;
goto _start;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
x_37 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(x_36, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_3 = x_14;
x_4 = x_38;
x_8 = x_39;
goto _start;
}
default: 
{
x_3 = x_14;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_st_ref_take(x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_Parser_addSyntaxNodeKind(x_19, x_12);
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_st_ref_set(x_7, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_3 = x_14;
x_4 = x_23;
x_8 = x_22;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_27 = lean_ctor_get(x_16, 2);
x_28 = lean_ctor_get(x_16, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_29 = l_Lean_Parser_addSyntaxNodeKind(x_25, x_12);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
x_31 = lean_st_ref_set(x_7, x_30, x_17);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_3 = x_14;
x_4 = x_33;
x_8 = x_32;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(x_7, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6(x_10, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parser_getParserPriority(x_3);
x_10 = l_Lean_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(x_9, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = l_Lean_Parser_parserExtension;
x_19 = l_Lean_PersistentEnvExtension_getState___rarg(x_18, x_16);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_20);
x_21 = l_Lean_Parser_mkParserOfConstant(x_16, x_17, x_20, x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_24, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_30, x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_33 = l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(x_2, x_32, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_37 = lean_apply_1(x_35, x_36);
x_38 = lean_box(0);
x_39 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(x_37, x_38, x_5, x_6, x_7, x_34);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_unbox(x_27);
lean_inc(x_11);
lean_inc(x_28);
lean_inc(x_1);
x_42 = l_Lean_Parser_addParser(x_20, x_1, x_2, x_41, x_28, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_45, x_5, x_6, x_7, x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_42);
x_51 = lean_st_ref_take(x_7, x_40);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_2);
lean_inc(x_1);
x_56 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_28);
lean_ctor_set(x_56, 3, x_11);
x_57 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_57);
x_58 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_18, x_55, x_56);
lean_ctor_set(x_52, 0, x_58);
x_59 = lean_st_ref_set(x_7, x_52, x_53);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = 0;
x_62 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_61, x_5, x_6, x_7, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
x_65 = lean_ctor_get(x_52, 2);
x_66 = lean_ctor_get(x_52, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
lean_inc(x_2);
lean_inc(x_1);
x_67 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set(x_67, 2, x_28);
lean_ctor_set(x_67, 3, x_11);
x_68 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_68);
x_69 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_18, x_63, x_67);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_66);
x_71 = lean_st_ref_set(x_7, x_70, x_53);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = 0;
x_74 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_73, x_5, x_6, x_7, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_33);
if (x_75 == 0)
{
return x_33;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_33, 0);
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_33);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_10);
if (x_79 == 0)
{
return x_10;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_10, 0);
x_81 = lean_ctor_get(x_10, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_10);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser");
return x_1;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_mkParserAttributeImpl___closed__1;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed), 8, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserAttributeImpl___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_mkParserAttributeImpl(x_1, x_2);
x_5 = l_Lean_registerBuiltinAttribute(x_4, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 2)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_apply_1(x_3, x_1);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser attribute implementation builder arguments");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Parser_mkParserAttributeImpl(x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_12 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_13;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_14;
}
}
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parserAttr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2;
x_3 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__3;
x_4 = l_Lean_registerAttributeImplBuilder(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_registerParserCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_6 = l_Lean_Parser_addParserCategory(x_1, x_3, x_4);
x_7 = l_IO_ofExcept___at_Lean_KeyedDeclsAttribute_declareBuiltin___spec__1(x_6, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2;
x_16 = l_Lean_registerAttributeOfBuilder(x_8, x_15, x_14, x_9);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_registerParserCategory(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTermParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__2;
x_3 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__2;
x_3 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCommandParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_commandParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_notFollowedByCategoryTokenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = l_Lean_Parser_parserExtension;
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_4);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_9 = l_System_FilePath_dirName___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
lean_inc(x_2);
x_17 = l_Lean_Parser_peekToken(x_2, x_3);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 2)
{
uint8_t x_21; 
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
lean_dec(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_name_mk_string(x_26, x_23);
x_28 = l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_1);
x_31 = l_Lean_Parser_ParserState_mkUnexpectedError(x_22, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_Parser_mkAntiquot___closed__8;
x_35 = lean_string_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = lean_name_mk_string(x_38, x_33);
x_40 = l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_40);
x_41 = l_System_FilePath_dirName___closed__1;
x_42 = l_Lean_Name_toStringWithSep___main(x_41, x_1);
x_43 = l_Lean_Parser_ParserState_mkUnexpectedError(x_32, x_42);
return x_43;
}
}
else
{
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_1);
return x_32;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
return x_44;
}
}
}
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_notFollowedByCategoryTokenFn___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_notFollowedByCategoryToken(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_Lean_Parser_Basic___instance__8___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByCommandToken___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByCommandToken___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Lean_Parser_Basic___instance__8___closed__1;
x_2 = l_Lean_Parser_notFollowedByCommandToken___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByCommandToken() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_notFollowedByCommandToken___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByTermToken___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByCategoryTokenFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByTermToken___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Lean_Parser_Basic___instance__8___closed__1;
x_2 = l_Lean_Parser_notFollowedByTermToken___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByTermToken() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_notFollowedByTermToken___closed__2;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_Parser_StrInterpolation(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Extension(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_StrInterpolation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
lean_dec_ref(res);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_22_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinSyntaxNodeKindSetRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinSyntaxNodeKindSetRef);
lean_dec_ref(res);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_98_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinParserCategoriesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinParserCategoriesRef);
lean_dec_ref(res);
l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2);
l_Lean_Parser_ParserExtensionState_tokens___default = _init_l_Lean_Parser_ParserExtensionState_tokens___default();
lean_mark_persistent(l_Lean_Parser_ParserExtensionState_tokens___default);
l_Lean_Parser_ParserExtensionState_kinds___default = _init_l_Lean_Parser_ParserExtensionState_kinds___default();
lean_mark_persistent(l_Lean_Parser_ParserExtensionState_kinds___default);
l_Lean_Parser_ParserExtensionState_categories___default = _init_l_Lean_Parser_ParserExtensionState_categories___default();
lean_mark_persistent(l_Lean_Parser_ParserExtensionState_categories___default);
l_Lean_Parser_ParserExtensionState_newEntries___default = _init_l_Lean_Parser_ParserExtensionState_newEntries___default();
lean_mark_persistent(l_Lean_Parser_ParserExtensionState_newEntries___default);
l_Lean_Parser_Lean_Parser_Extension___instance__1___closed__1 = _init_l_Lean_Parser_Lean_Parser_Extension___instance__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Lean_Parser_Extension___instance__1___closed__1);
l_Lean_Parser_Lean_Parser_Extension___instance__1 = _init_l_Lean_Parser_Lean_Parser_Extension___instance__1();
lean_mark_persistent(l_Lean_Parser_Lean_Parser_Extension___instance__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2);
l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1 = _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__3);
l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtensionAddEntry___closed__4);
l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1 = _init_l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__1);
l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2 = _init_l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__2);
l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3 = _init_l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe_match__1___rarg___closed__3);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__1 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__2 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__2();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2);
l_Lean_Parser_compileParserDescr_visit___closed__1 = _init_l_Lean_Parser_compileParserDescr_visit___closed__1();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__1);
l_Lean_Parser_compileParserDescr_visit___closed__2 = _init_l_Lean_Parser_compileParserDescr_visit___closed__2();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__2);
l_Lean_Parser_compileParserDescr_visit___closed__3 = _init_l_Lean_Parser_compileParserDescr_visit___closed__3();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__3);
l_Lean_Parser_compileParserDescr_visit___closed__4 = _init_l_Lean_Parser_compileParserDescr_visit___closed__4();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__4);
l_Lean_Parser_compileParserDescr_visit___closed__5 = _init_l_Lean_Parser_compileParserDescr_visit___closed__5();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__5);
l_Lean_Parser_compileParserDescr_visit___closed__6 = _init_l_Lean_Parser_compileParserDescr_visit___closed__6();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__6);
l_Lean_Parser_compileParserDescr_visit___closed__7 = _init_l_Lean_Parser_compileParserDescr_visit___closed__7();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__7);
l_Lean_Parser_compileParserDescr_visit___closed__8 = _init_l_Lean_Parser_compileParserDescr_visit___closed__8();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__8);
l_Lean_Parser_compileParserDescr_visit___closed__9 = _init_l_Lean_Parser_compileParserDescr_visit___closed__9();
lean_mark_persistent(l_Lean_Parser_compileParserDescr_visit___closed__9);
res = l_Lean_Parser_mkParserAttributeHooks(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAttributeHooks = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAttributeHooks);
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__1___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____lambda__2___closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598____closed__6);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1598_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____lambda__2___closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654____closed__6);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1654_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__6);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__7 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__7();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__7);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__8 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__8();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863____closed__8);
l_Lean_Parser_parserExtension___closed__1 = _init_l_Lean_Parser_parserExtension___closed__1();
lean_mark_persistent(l_Lean_Parser_parserExtension___closed__1);
l_Lean_Parser_parserExtension___closed__2 = _init_l_Lean_Parser_parserExtension___closed__2();
lean_mark_persistent(l_Lean_Parser_parserExtension___closed__2);
l_Lean_Parser_parserExtension___closed__3 = _init_l_Lean_Parser_parserExtension___closed__3();
lean_mark_persistent(l_Lean_Parser_parserExtension___closed__3);
l_Lean_Parser_parserExtension___closed__4 = _init_l_Lean_Parser_parserExtension___closed__4();
lean_mark_persistent(l_Lean_Parser_parserExtension___closed__4);
l_Lean_Parser_parserExtension___closed__5 = _init_l_Lean_Parser_parserExtension___closed__5();
lean_mark_persistent(l_Lean_Parser_parserExtension___closed__5);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1863_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserExtension);
lean_dec_ref(res);
l_Lean_Parser_categoryParserFnImpl___closed__1 = _init_l_Lean_Parser_categoryParserFnImpl___closed__1();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__1);
l_Lean_Parser_categoryParserFnImpl___closed__2 = _init_l_Lean_Parser_categoryParserFnImpl___closed__2();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__2);
l_Lean_Parser_categoryParserFnImpl___closed__3 = _init_l_Lean_Parser_categoryParserFnImpl___closed__3();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__3);
l_Lean_Parser_categoryParserFnImpl___closed__4 = _init_l_Lean_Parser_categoryParserFnImpl___closed__4();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__4);
l_Lean_Parser_setCategoryParserFnRef___closed__1 = _init_l_Lean_Parser_setCategoryParserFnRef___closed__1();
lean_mark_persistent(l_Lean_Parser_setCategoryParserFnRef___closed__1);
res = l_Lean_Parser_setCategoryParserFnRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_declareBuiltinParser___closed__1 = _init_l_Lean_Parser_declareBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__1);
l_Lean_Parser_declareBuiltinParser___closed__2 = _init_l_Lean_Parser_declareBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__2);
l_Lean_Parser_declareBuiltinParser___closed__3 = _init_l_Lean_Parser_declareBuiltinParser___closed__3();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__3);
l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__1);
l_Lean_Parser_declareLeadingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__2);
l_Lean_Parser_declareTrailingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__1);
l_Lean_Parser_declareTrailingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__2);
l_Lean_Parser_getParserPriority___closed__1 = _init_l_Lean_Parser_getParserPriority___closed__1();
lean_mark_persistent(l_Lean_Parser_getParserPriority___closed__1);
l_Lean_Parser_getParserPriority___closed__2 = _init_l_Lean_Parser_getParserPriority___closed__2();
lean_mark_persistent(l_Lean_Parser_getParserPriority___closed__2);
l_Lean_Parser_getParserPriority___closed__3 = _init_l_Lean_Parser_getParserPriority___closed__3();
lean_mark_persistent(l_Lean_Parser_getParserPriority___closed__3);
l_Lean_Parser_getParserPriority___closed__4 = _init_l_Lean_Parser_getParserPriority___closed__4();
lean_mark_persistent(l_Lean_Parser_getParserPriority___closed__4);
l_Lean_Parser_getParserPriority___closed__5 = _init_l_Lean_Parser_getParserPriority___closed__5();
lean_mark_persistent(l_Lean_Parser_getParserPriority___closed__5);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3);
l_Lean_Parser_registerBuiltinParserAttribute___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1 = _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1);
l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2 = _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2);
l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3 = _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3);
l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4 = _init_l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4);
l_Lean_Parser_mkParserAttributeImpl___closed__1 = _init_l_Lean_Parser_mkParserAttributeImpl___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserAttributeImpl___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___lambda__1___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder___closed__3);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_registerParserAttributeImplBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103____closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3103_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113____closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3113_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133____closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3133_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_notFollowedByCommandToken___closed__1 = _init_l_Lean_Parser_notFollowedByCommandToken___closed__1();
lean_mark_persistent(l_Lean_Parser_notFollowedByCommandToken___closed__1);
l_Lean_Parser_notFollowedByCommandToken___closed__2 = _init_l_Lean_Parser_notFollowedByCommandToken___closed__2();
lean_mark_persistent(l_Lean_Parser_notFollowedByCommandToken___closed__2);
l_Lean_Parser_notFollowedByCommandToken = _init_l_Lean_Parser_notFollowedByCommandToken();
lean_mark_persistent(l_Lean_Parser_notFollowedByCommandToken);
l_Lean_Parser_notFollowedByTermToken___closed__1 = _init_l_Lean_Parser_notFollowedByTermToken___closed__1();
lean_mark_persistent(l_Lean_Parser_notFollowedByTermToken___closed__1);
l_Lean_Parser_notFollowedByTermToken___closed__2 = _init_l_Lean_Parser_notFollowedByTermToken___closed__2();
lean_mark_persistent(l_Lean_Parser_notFollowedByTermToken___closed__2);
l_Lean_Parser_notFollowedByTermToken = _init_l_Lean_Parser_notFollowedByTermToken();
lean_mark_persistent(l_Lean_Parser_notFollowedByTermToken);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
