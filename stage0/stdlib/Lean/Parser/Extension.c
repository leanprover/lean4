// Lean compiler output
// Module: Lean.Parser.Extension
// Imports: Init Lean.Parser.Basic Lean.PrettyPrinter.Parenthesizer
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
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
lean_object* l_Lean_Parser_builtinTokenTable;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_mkParserExtension___closed__1;
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Parser_addLeadingParser___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingIdentAsSymbol___boxed(lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserContext(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_7__addTrailingParserAux(lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_6__addTokenConfig___closed__2;
lean_object* l_List_foldlM___main___at_Lean_Parser_addParserTokens___spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_charLit;
lean_object* l_Lean_Parser_trailingLoop___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Environment_contains___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
lean_object* l_Lean_Parser_parserExtension___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___closed__4;
lean_object* l_Lean_Parser_getTokenTable___boxed(lean_object*);
lean_object* l___private_Lean_Parser_Extension_6__addTokenConfig___closed__1;
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Parser_addLeadingParser___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addParser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Parser_categoryParserFnRef;
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1;
lean_object* l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserExtensionState_inhabited___closed__1;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Parser_regTermParserAttribute(lean_object*);
lean_object* l_Lean_Parser_builtinParserCategoriesRef;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_parserExtension___closed__2;
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__1;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___lambda__2(lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__5;
lean_object* l_List_map___main___at_Lean_Parser_addLeadingParser___spec__4(lean_object*);
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__1;
lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_4__addBuiltinParserCategory(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Parser_Extension_8__updateBuiltinTokens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2;
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__4___rarg(lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_6__addTokenConfig(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1;
lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___closed__1;
lean_object* l_Lean_Parser_parserExtension___closed__1;
lean_object* l_Lean_Parser_declareBuiltinParser___closed__4;
extern lean_object* l_Lean_nameLitKind;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addParserCategory(lean_object*, lean_object*, uint8_t);
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Parser_parserExtension___closed__3;
lean_object* l_Lean_Parser_parserExtension___elambda__2___boxed(lean_object*);
uint8_t l_Std_PersistentHashMap_containsAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
lean_object* l_List_foldl___main___at___private_Lean_Parser_Extension_7__addTrailingParserAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___lambda__1(lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
lean_object* l_Lean_Parser_parserExtension___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_leadingIdentAsSymbol(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAttributeImplOfConstant___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setCategoryParserFnRef(lean_object*);
lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object*);
extern lean_object* l_Lean_Parser_PrattParsingTables_inhabited___closed__1;
lean_object* l_Lean_Parser_compileParserDescr___main___closed__3;
lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkBuiltinParserCategories(lean_object*);
lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1;
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
extern lean_object* l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
uint8_t l_Std_PersistentHashMap_containsAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_parserExtension___closed__6;
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_regTermParserAttribute___closed__1;
extern lean_object* l_Lean_KeyedDeclsAttribute_declareBuiltin___rarg___closed__4;
lean_object* l_Lean_Parser_mkParserExtension___closed__8;
lean_object* l_Lean_Parser_whitespace___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Parser_addToken(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Compiler_InitAttr_2__isUnitType___closed__1;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeImpl___closed__1;
extern lean_object* l_Lean_Parser_termParser___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_regTermParserAttribute___closed__2;
lean_object* l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined(lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserExtensionState_inhabited;
lean_object* l_Lean_Parser_compileParserDescr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setCategoryParserFnRef___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
extern lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
lean_object* l_Lean_Parser_parserExtension___elambda__2(lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_IO_Error_Inhabited___closed__1;
lean_object* l_Lean_Parser_compileParserDescr___main___closed__1;
lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1___boxed(lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Parser_Extension_4__addBuiltinParserCategory___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Parser_addLeadingParser___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Trie_2__insertAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserExtension(lean_object*);
lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkBuiltinTokenTable(lean_object*);
lean_object* l_Lean_Parser_addTrailingParser(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__6;
lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___closed__7;
lean_object* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Parser_parserExtension___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1;
lean_object* l___private_Lean_Parser_Extension_3__addParserCategoryCore(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__2;
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l___private_Lean_Parser_Extension_12__ParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_EqnCompiler_CaseArraySizes_2__introArrayLitAux___main___closed__3;
lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___closed__3;
extern lean_object* l_Lean_identKind;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_compileParserDescr___main___closed__2;
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tryFn(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__5;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toExprAux___main(lean_object*);
lean_object* l_Lean_Parser_mkParserExtension___closed__5;
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder(lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_builtinSyntaxNodeKindSetRef;
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState___boxed(lean_object*);
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* lean_io_ref_swap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compile(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Parser_Extension_5__ParserExtension_mkInitial(lean_object*);
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__1;
extern lean_object* l_Lean_KeyedDeclsAttribute_init___rarg___lambda__3___closed__1;
lean_object* l___private_Lean_Parser_Extension_10__ParserExtension_addImported___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTermParserAttr(lean_object*);
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstant(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__1(lean_object*);
lean_object* l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__2;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object*);
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_addParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_1__registerAuxiliaryNodeKindSets(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDupsAux___main___at_Lean_Parser_addLeadingParser___spec__6(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Lean_Parser_Extension_9__ParserExtension_addEntry(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_12__ParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getSyntaxNodeKinds___boxed(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Parser_addLeadingParser___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__4;
lean_object* l_List_eraseDups___at_Lean_Parser_addLeadingParser___spec__5(lean_object*);
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr___main___closed__4;
lean_object* l___private_Lean_Data_Trie_3__findAux_x3f___main___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__1;
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_initAttr;
lean_object* l_Std_PersistentHashMap_containsAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Extension_10__ParserExtension_addImported(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserExtension___elambda__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_compileParserDescr___main___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkBuiltinTokenTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_5, x_1, x_7);
x_9 = lean_io_ref_reset(x_3, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_io_ref_set(x_3, x_8, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_1__registerAuxiliaryNodeKindSets(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_choiceKind;
x_3 = l_Lean_Parser_registerBuiltinNodeKind(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_identKind;
x_6 = l_Lean_Parser_registerBuiltinNodeKind(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_strLitKind;
x_9 = l_Lean_Parser_registerBuiltinNodeKind(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_numLitKind;
x_12 = l_Lean_Parser_registerBuiltinNodeKind(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_charLitKind;
x_15 = l_Lean_Parser_registerBuiltinNodeKind(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_nameLitKind;
x_18 = l_Lean_Parser_registerBuiltinNodeKind(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_6);
if (x_41 == 0)
{
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_mkBuiltinParserCategories(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser category '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been defined");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg), 1, 0);
return x_2;
}
}
uint8_t l_Std_PersistentHashMap_containsAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Environment_contains___spec__5(x_17, x_18, x_3);
lean_dec(x_17);
return x_19;
}
}
}
uint8_t l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_38 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_75 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_71, x_73, x_74, x_4, x_5);
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
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__5(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__6(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_5, x_7, x_8, x_2, x_3);
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
x_16 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_12, x_14, x_15, x_2, x_3);
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
lean_object* l___private_Lean_Parser_Extension_3__addParserCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_1);
x_4 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg(x_2);
return x_7;
}
}
}
lean_object* l_Std_PersistentHashMap_containsAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__4(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Parser_Extension_4__addBuiltinParserCategory(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_builtinParserCategoriesRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Parser_PrattParsingTables_inhabited___closed__1;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_2);
x_10 = l___private_Lean_Parser_Extension_3__addParserCategoryCore(x_6, x_1, x_9);
x_11 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_10, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_ref_set(x_4, x_12, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Parser_Extension_4__addBuiltinParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Extension_4__addBuiltinParserCategory(x_1, x_4, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_ParserExtensionState_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1;
x_4 = l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_ParserExtensionState_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParserExtensionState_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_5__ParserExtension_mkInitial(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_builtinTokenTable;
x_3 = lean_io_ref_get(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
x_7 = lean_io_ref_get(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Parser_builtinParserCategoriesRef;
x_11 = lean_io_ref_get(x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* _init_l___private_Lean_Parser_Extension_6__addTokenConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid empty symbol");
return x_1;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_6__addTokenConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_6__addTokenConfig___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_6__addTokenConfig(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Lean_Data_Trie_3__findAux_x3f___main___rarg(x_2, x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l___private_Lean_Data_Trie_2__insertAux___main___rarg(x_2, x_2, x_1, x_5);
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
x_10 = l___private_Lean_Parser_Extension_6__addTokenConfig___closed__2;
return x_10;
}
}
}
lean_object* _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1() {
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
x_2 = l_Lean_Name_toString___closed__1;
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
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Parser_addLeadingParser___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Parser_addLeadingParser___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Parser_addLeadingParser___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Parser_addLeadingParser___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_List_map___main___at_Lean_Parser_addLeadingParser___spec__4(lean_object* x_1) {
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
x_8 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__4(x_5);
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
x_13 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__4(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_eraseDupsAux___main___at_Lean_Parser_addLeadingParser___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_5, x_2);
if (x_7 == 0)
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
}
}
}
}
lean_object* l_List_eraseDups___at_Lean_Parser_addLeadingParser___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_eraseDupsAux___main___at_Lean_Parser_addLeadingParser___spec__6(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_8 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_4, x_1);
lean_ctor_set(x_2, 0, x_8);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Parser_TokenMap_insert___rarg(x_10, x_4, x_1);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_2 = x_15;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_Lean_Parser_addLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_37; lean_object* x_53; lean_object* x_54; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_53 = lean_ctor_get(x_4, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
lean_dec(x_53);
switch (lean_obj_tag(x_54)) {
case 2:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_37 = x_55;
goto block_52;
}
case 3:
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_37 = x_56;
goto block_52;
}
default: 
{
lean_object* x_57; 
lean_dec(x_54);
x_57 = lean_box(0);
x_8 = x_57;
goto block_36;
}
}
block_36:
{
uint8_t x_9; 
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_10, 1, x_13);
x_14 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_7, 0, x_21);
x_22 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_7);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_27);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 4, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_25);
x_34 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
block_52:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__4(x_37);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = l_List_eraseDups___at_Lean_Parser_addLeadingParser___spec__5(x_38);
x_42 = l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__7(x_4, x_40, x_41);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_7);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_45);
lean_dec(x_7);
x_47 = l_List_eraseDups___at_Lean_Parser_addLeadingParser___spec__5(x_38);
x_48 = l_List_foldl___main___at_Lean_Parser_addLeadingParser___spec__7(x_4, x_45, x_47);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_46);
x_50 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Parser_addLeadingParser___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Parser_addLeadingParser___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Parser_addLeadingParser___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Parser_addLeadingParser___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_addLeadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_addLeadingParser(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Parser_Extension_7__addTrailingParserAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_8 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_4, x_1);
lean_ctor_set(x_2, 2, x_8);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Parser_TokenMap_insert___rarg(x_12, x_4, x_1);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_13);
x_2 = x_15;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_7__addTrailingParserAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_14; lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
switch (lean_obj_tag(x_20)) {
case 2:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_14 = x_21;
goto block_18;
}
case 3:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_14 = x_22;
goto block_18;
}
default: 
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_box(0);
x_3 = x_23;
goto block_13;
}
}
block_13:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_1, 3, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_List_map___main___at_Lean_Parser_addLeadingParser___spec__4(x_14);
x_16 = l_List_eraseDups___at_Lean_Parser_addLeadingParser___spec__5(x_15);
x_17 = l_List_foldl___main___at___private_Lean_Parser_Extension_7__addTrailingParserAux___spec__1(x_2, x_1, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_addTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l___private_Lean_Parser_Extension_7__addTrailingParserAux(x_8, x_3);
lean_ctor_set(x_6, 0, x_9);
x_10 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_12);
lean_dec(x_6);
x_14 = l___private_Lean_Parser_Extension_7__addTrailingParserAux(x_12, x_3);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_13);
x_16 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_1, x_2, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Parser_addParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Parser_addTrailingParser(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_Parser_addLeadingParser(x_1, x_2, x_3, x_5);
return x_7;
}
}
}
lean_object* l_Lean_Parser_addParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_addParser(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
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
x_6 = l___private_Lean_Parser_Extension_6__addTokenConfig(x_1, x_4);
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
lean_object* _init_l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin parser '");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_8__updateBuiltinTokens(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_builtinTokenTable;
x_5 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_6 = lean_io_ref_swap(x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Parser_addParserTokens(x_8, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_2);
x_14 = l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_6);
lean_dec(x_2);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_io_ref_set(x_4, x_20, x_9);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = l_Lean_Parser_addParserTokens(x_22, x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_2);
x_28 = l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_25);
lean_dec(x_25);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_io_ref_set(x_4, x_35, x_23);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
return x_6;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_builtinParserCategoriesRef;
x_7 = lean_io_ref_get(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l_Lean_Parser_addParser(x_8, x_1, x_2, x_3, x_4);
x_11 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_10, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_io_ref_set(x_6, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
x_19 = lean_io_ref_get(x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_1(x_15, x_20);
x_23 = lean_io_ref_reset(x_18, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_io_ref_set(x_18, x_22, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l___private_Lean_Parser_Extension_8__updateBuiltinTokens(x_14, x_2, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Parser_Extension_9__ParserExtension_addEntry(lean_object* x_1, lean_object* x_2) {
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
x_9 = l___private_Lean_Parser_Extension_6__addTokenConfig(x_5, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_10 = l_Lean_Parser_ParserExtensionState_inhabited;
x_11 = l_unreachable_x21___rarg(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_1, 3, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_3);
x_19 = l___private_Lean_Parser_Extension_6__addTokenConfig(x_15, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
x_20 = l_Lean_Parser_ParserExtensionState_inhabited;
x_21 = l_unreachable_x21___rarg(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_24);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_box(0);
lean_inc(x_26);
x_31 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_28, x_26, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_1, 3, x_33);
lean_ctor_set(x_1, 1, x_31);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_38 = lean_box(0);
lean_inc(x_26);
x_39 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_35, x_26, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_41);
return x_42;
}
}
case 2:
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_inc(x_47);
x_49 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1(x_47, x_43);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_1, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_1, 0);
lean_dec(x_54);
x_55 = l_Lean_Parser_PrattParsingTables_inhabited___closed__1;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_44);
lean_inc(x_43);
x_57 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_47, x_43, x_56);
x_58 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_44);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_48);
lean_ctor_set(x_1, 3, x_59);
lean_ctor_set(x_1, 2, x_57);
return x_1;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_1);
x_60 = l_Lean_Parser_PrattParsingTables_inhabited___closed__1;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_44);
lean_inc(x_43);
x_62 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__3(x_47, x_43, x_61);
x_63 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_63, 0, x_43);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_44);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_45);
lean_ctor_set(x_65, 1, x_46);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_64);
return x_65;
}
}
else
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
return x_1;
}
}
default: 
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_1);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_1, 0);
x_72 = lean_ctor_get(x_1, 1);
x_73 = lean_ctor_get(x_1, 2);
x_74 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
x_75 = l_Lean_Parser_addParser(x_73, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_75);
lean_free_object(x_1);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_66);
x_76 = l_Lean_Parser_ParserExtensionState_inhabited;
x_77 = l_unreachable_x21___rarg(x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_67);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_1, 3, x_80);
lean_ctor_set(x_1, 2, x_78);
return x_1;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_1, 0);
x_82 = lean_ctor_get(x_1, 1);
x_83 = lean_ctor_get(x_1, 2);
x_84 = lean_ctor_get(x_1, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_1);
lean_inc(x_66);
x_85 = l_Lean_Parser_addParser(x_83, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_67);
lean_dec(x_66);
x_86 = l_Lean_Parser_ParserExtensionState_inhabited;
x_87 = l_unreachable_x21___rarg(x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_67);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_82);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_90);
return x_91;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parser type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParserDescr");
return x_1;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_14; 
lean_inc(x_3);
lean_inc(x_1);
x_14 = lean_environment_find(x_1, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_1);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_3);
x_17 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_ConstantInfo_type(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_mkAppStx___closed__1;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_1);
x_31 = lean_box(0);
x_5 = x_31;
goto block_13;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_33 = lean_string_dec_eq(x_27, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
x_35 = lean_string_dec_eq(x_27, x_34);
lean_dec(x_27);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_1);
x_36 = lean_box(0);
x_5 = x_36;
goto block_13;
}
else
{
lean_object* x_37; 
x_37 = lean_eval_const(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_apply_1(x_4, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = 0;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_27);
x_56 = lean_eval_const(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_apply_1(x_4, x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = 1;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_61, 0, x_69);
return x_61;
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_61, 0);
lean_inc(x_70);
lean_dec(x_61);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
}
}
case 1:
{
lean_object* x_75; 
lean_dec(x_4);
x_75 = lean_ctor_get(x_26, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_24, 1);
lean_inc(x_76);
lean_dec(x_24);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
lean_dec(x_25);
x_78 = lean_ctor_get(x_26, 1);
lean_inc(x_78);
lean_dec(x_26);
x_79 = l_Lean_mkAppStx___closed__1;
x_80 = lean_string_dec_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_1);
x_81 = lean_box(0);
x_5 = x_81;
goto block_13;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_mkAppStx___closed__3;
x_83 = lean_string_dec_eq(x_77, x_82);
lean_dec(x_77);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_76);
lean_dec(x_1);
x_84 = lean_box(0);
x_5 = x_84;
goto block_13;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1;
x_86 = lean_string_dec_eq(x_76, x_85);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = lean_string_dec_eq(x_76, x_82);
lean_dec(x_76);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_1);
x_88 = lean_box(0);
x_5 = x_88;
goto block_13;
}
else
{
lean_object* x_89; 
x_89 = lean_eval_const(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
x_95 = 1;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_89, 0, x_97);
return x_89;
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_89, 0);
lean_inc(x_98);
lean_dec(x_89);
x_99 = 1;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_76);
x_103 = lean_eval_const(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_103, 0);
x_109 = 0;
x_110 = lean_box(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_103, 0, x_111);
return x_103;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
lean_dec(x_103);
x_113 = 0;
x_114 = lean_box(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
}
}
}
else
{
lean_object* x_117; 
lean_dec(x_75);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_117 = lean_box(0);
x_5 = x_117;
goto block_13;
}
}
default: 
{
lean_object* x_118; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_1);
x_118 = lean_box(0);
x_5 = x_118;
goto block_13;
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_1);
x_119 = lean_box(0);
x_5 = x_119;
goto block_13;
}
}
else
{
lean_object* x_120; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_1);
x_120 = lean_box(0);
x_5 = x_120;
goto block_13;
}
}
else
{
lean_object* x_121; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_box(0);
x_5 = x_121;
goto block_13;
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_3);
x_8 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkParserOfConstantUnsafe(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAttributeImplOfConstant___closed__1;
return x_5;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkParserOfConstantAux(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_compileParserDescr___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_numLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_compileParserDescr___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_compileParserDescr___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_compileParserDescr___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLit;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_compileParserDescr___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_compileParserDescr___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Lean_Parser_andthenInfo(x_17, x_18);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = l_Lean_Parser_andthenInfo(x_25, x_26);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_33);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_34);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_34);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = l_Lean_Parser_orelseInfo(x_46, x_47);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_51, 0, x_49);
lean_closure_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_40, 0, x_52);
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = l_Lean_Parser_orelseInfo(x_54, x_55);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec(x_3);
x_63 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = l_Lean_Parser_optionaInfo(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_63, 0, x_73);
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_63, 0);
lean_inc(x_74);
lean_dec(x_63);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = l_Lean_Parser_optionaInfo(x_75);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
case 3:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_3, 0);
lean_inc(x_81);
lean_dec(x_3);
x_82 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_81);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 1);
x_90 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_90, 0, x_89);
lean_ctor_set(x_87, 1, x_90);
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_82, 0, x_94);
return x_82;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
lean_dec(x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_99, 0, x_97);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
case 4:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_3, 0);
lean_inc(x_102);
lean_dec(x_3);
x_103 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_103, 0);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 1);
x_111 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn), 3, 1);
lean_closure_set(x_111, 0, x_110);
lean_ctor_set(x_108, 1, x_111);
return x_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn), 3, 1);
lean_closure_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_103, 0, x_115);
return x_103;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_103, 0);
lean_inc(x_116);
lean_dec(x_103);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn), 3, 1);
lean_closure_set(x_120, 0, x_118);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
case 5:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_3, 0);
lean_inc(x_123);
lean_dec(x_3);
x_124 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_123);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_124, 0);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = l_Lean_Parser_noFirstTokenInfo(x_130);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_124, 0, x_134);
return x_124;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_124, 0);
lean_inc(x_135);
lean_dec(x_124);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = l_Lean_Parser_noFirstTokenInfo(x_136);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
case 6:
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_3, 0);
lean_inc(x_142);
lean_dec(x_3);
x_143 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_142);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_143);
if (x_147 == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_143, 0);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_148, 1);
x_151 = 0;
x_152 = lean_box(x_151);
x_153 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn___boxed), 4, 2);
lean_closure_set(x_153, 0, x_150);
lean_closure_set(x_153, 1, x_152);
lean_ctor_set(x_148, 1, x_153);
return x_143;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_148, 0);
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_148);
x_156 = 0;
x_157 = lean_box(x_156);
x_158 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn___boxed), 4, 2);
lean_closure_set(x_158, 0, x_155);
lean_closure_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_143, 0, x_159);
return x_143;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_160 = lean_ctor_get(x_143, 0);
lean_inc(x_160);
lean_dec(x_143);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = 0;
x_165 = lean_box(x_164);
x_166 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn___boxed), 4, 2);
lean_closure_set(x_166, 0, x_162);
lean_closure_set(x_166, 1, x_165);
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
case 7:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_3, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_3, 1);
lean_inc(x_170);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_171 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_169);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
lean_dec(x_170);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_171, 0);
lean_inc(x_175);
lean_dec(x_171);
x_176 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_170);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
lean_dec(x_175);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
return x_176;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_176);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_176, 0);
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = l_Lean_Parser_sepByInfo(x_182, x_183);
x_185 = lean_ctor_get(x_175, 1);
lean_inc(x_185);
lean_dec(x_175);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = 0;
x_188 = lean_box(x_187);
x_189 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(x_189, 0, x_188);
lean_closure_set(x_189, 1, x_185);
lean_closure_set(x_189, 2, x_186);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_184);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_176, 0, x_190);
return x_176;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_191 = lean_ctor_get(x_176, 0);
lean_inc(x_191);
lean_dec(x_176);
x_192 = lean_ctor_get(x_175, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = l_Lean_Parser_sepByInfo(x_192, x_193);
x_195 = lean_ctor_get(x_175, 1);
lean_inc(x_195);
lean_dec(x_175);
x_196 = lean_ctor_get(x_191, 1);
lean_inc(x_196);
lean_dec(x_191);
x_197 = 0;
x_198 = lean_box(x_197);
x_199 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(x_199, 0, x_198);
lean_closure_set(x_199, 1, x_195);
lean_closure_set(x_199, 2, x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_194);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
}
case 8:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_3, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_3, 1);
lean_inc(x_203);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_204 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_202);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
lean_dec(x_203);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_204, 0);
lean_inc(x_208);
lean_dec(x_204);
x_209 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_203);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
lean_dec(x_208);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_209);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_209, 0);
x_215 = lean_ctor_get(x_208, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = l_Lean_Parser_sepBy1Info(x_215, x_216);
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
lean_dec(x_208);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
lean_dec(x_214);
x_220 = 0;
x_221 = lean_box(x_220);
x_222 = lean_box(x_220);
x_223 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 6, 4);
lean_closure_set(x_223, 0, x_221);
lean_closure_set(x_223, 1, x_218);
lean_closure_set(x_223, 2, x_219);
lean_closure_set(x_223, 3, x_222);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_217);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_209, 0, x_224);
return x_209;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_225 = lean_ctor_get(x_209, 0);
lean_inc(x_225);
lean_dec(x_209);
x_226 = lean_ctor_get(x_208, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
x_228 = l_Lean_Parser_sepBy1Info(x_226, x_227);
x_229 = lean_ctor_get(x_208, 1);
lean_inc(x_229);
lean_dec(x_208);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
x_231 = 0;
x_232 = lean_box(x_231);
x_233 = lean_box(x_231);
x_234 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 6, 4);
lean_closure_set(x_234, 0, x_232);
lean_closure_set(x_234, 1, x_229);
lean_closure_set(x_234, 2, x_230);
lean_closure_set(x_234, 3, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_228);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
}
}
}
case 9:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_3, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_3, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_3, 2);
lean_inc(x_239);
lean_dec(x_3);
x_240 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_239);
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_241; 
lean_dec(x_238);
lean_dec(x_237);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
return x_240;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
}
}
else
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_240);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_245 = lean_ctor_get(x_240, 0);
x_246 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_246, 0, x_238);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_inc(x_237);
x_248 = l_Lean_Parser_nodeInfo(x_237, x_247);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_250, 0, x_237);
lean_closure_set(x_250, 1, x_249);
x_251 = l_Lean_Parser_epsilonInfo;
x_252 = l_Lean_Parser_andthenInfo(x_251, x_248);
x_253 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_253, 0, x_246);
lean_closure_set(x_253, 1, x_250);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set(x_240, 0, x_254);
return x_240;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_255 = lean_ctor_get(x_240, 0);
lean_inc(x_255);
lean_dec(x_240);
x_256 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_256, 0, x_238);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
lean_inc(x_237);
x_258 = l_Lean_Parser_nodeInfo(x_237, x_257);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_260 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_260, 0, x_237);
lean_closure_set(x_260, 1, x_259);
x_261 = l_Lean_Parser_epsilonInfo;
x_262 = l_Lean_Parser_andthenInfo(x_261, x_258);
x_263 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_263, 0, x_256);
lean_closure_set(x_263, 1, x_260);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
return x_265;
}
}
}
case 10:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_3, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_3, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_3, 2);
lean_inc(x_268);
lean_dec(x_3);
x_269 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_268);
if (lean_obj_tag(x_269) == 0)
{
uint8_t x_270; 
lean_dec(x_267);
lean_dec(x_266);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
return x_269;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
else
{
uint8_t x_273; 
x_273 = !lean_is_exclusive(x_269);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_274 = lean_ctor_get(x_269, 0);
x_275 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_275, 0, x_267);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
lean_inc(x_266);
x_277 = l_Lean_Parser_nodeInfo(x_266, x_276);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec(x_274);
x_279 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_279, 0, x_266);
lean_closure_set(x_279, 1, x_278);
x_280 = l_Lean_Parser_epsilonInfo;
x_281 = l_Lean_Parser_andthenInfo(x_280, x_277);
x_282 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_282, 0, x_275);
lean_closure_set(x_282, 1, x_279);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_269, 0, x_283);
return x_269;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_284 = lean_ctor_get(x_269, 0);
lean_inc(x_284);
lean_dec(x_269);
x_285 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_285, 0, x_267);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_inc(x_266);
x_287 = l_Lean_Parser_nodeInfo(x_266, x_286);
x_288 = lean_ctor_get(x_284, 1);
lean_inc(x_288);
lean_dec(x_284);
x_289 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_289, 0, x_266);
lean_closure_set(x_289, 1, x_288);
x_290 = l_Lean_Parser_epsilonInfo;
x_291 = l_Lean_Parser_andthenInfo(x_290, x_287);
x_292 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_292, 0, x_285);
lean_closure_set(x_292, 1, x_289);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
case 11:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_ctor_get(x_3, 0);
lean_inc(x_295);
lean_dec(x_3);
x_296 = l_String_trim(x_295);
lean_dec(x_295);
lean_inc(x_296);
x_297 = l_Lean_Parser_symbolInfo(x_296);
x_298 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_298, 0, x_296);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
case 12:
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_2);
lean_dec(x_1);
x_301 = lean_ctor_get(x_3, 0);
lean_inc(x_301);
x_302 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_303 = l_String_trim(x_301);
lean_dec(x_301);
lean_inc(x_303);
x_304 = l_Lean_Parser_nonReservedSymbolInfo(x_303, x_302);
x_305 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_305, 0, x_303);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
case 13:
{
lean_object* x_308; 
lean_dec(x_2);
lean_dec(x_1);
x_308 = l_Lean_Parser_compileParserDescr___main___closed__1;
return x_308;
}
case 14:
{
lean_object* x_309; 
lean_dec(x_2);
lean_dec(x_1);
x_309 = l_Lean_Parser_compileParserDescr___main___closed__2;
return x_309;
}
case 15:
{
lean_object* x_310; 
lean_dec(x_2);
lean_dec(x_1);
x_310 = l_Lean_Parser_compileParserDescr___main___closed__3;
return x_310;
}
case 16:
{
lean_object* x_311; 
lean_dec(x_2);
lean_dec(x_1);
x_311 = l_Lean_Parser_compileParserDescr___main___closed__4;
return x_311;
}
case 17:
{
lean_object* x_312; 
lean_dec(x_2);
lean_dec(x_1);
x_312 = l_Lean_Parser_compileParserDescr___main___closed__5;
return x_312;
}
case 18:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_1);
x_313 = lean_ctor_get(x_3, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_3, 1);
lean_inc(x_314);
lean_dec(x_3);
x_315 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(x_2, x_313);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
lean_dec(x_314);
x_316 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_313);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_315);
x_317 = l_Lean_Parser_categoryParser(x_313, x_314);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
}
default: 
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_3, 0);
lean_inc(x_319);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_320 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr___main), 3, 2);
lean_closure_set(x_320, 0, x_1);
lean_closure_set(x_320, 1, x_2);
x_321 = l_Lean_Parser_mkParserOfConstantUnsafe(x_1, x_2, x_319, x_320);
lean_dec(x_2);
if (lean_obj_tag(x_321) == 0)
{
uint8_t x_322; 
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
return x_321;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_323);
return x_324;
}
}
else
{
uint8_t x_325; 
x_325 = !lean_is_exclusive(x_321);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_321, 0);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
lean_dec(x_326);
lean_ctor_set(x_321, 0, x_327);
return x_321;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_321, 0);
lean_inc(x_328);
lean_dec(x_321);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
}
}
}
}
}
lean_object* l_Lean_Parser_compileParserDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_compileParserDescr___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Parser_mkParserOfConstantUnsafe(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_3, x_4);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = l___private_Lean_Parser_Extension_6__addTokenConfig(x_15, x_13);
x_20 = l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1(x_19, x_6);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_5, 0, x_21);
x_4 = x_12;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_free_object(x_5);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_32 = l___private_Lean_Parser_Extension_6__addTokenConfig(x_28, x_13);
x_33 = l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1(x_32, x_6);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
x_4 = x_12;
x_5 = x_36;
x_6 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_1);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
case 1:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_5, 1);
x_45 = lean_box(0);
x_46 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_44, x_42, x_45);
lean_ctor_set(x_5, 1, x_46);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
x_50 = lean_ctor_get(x_5, 2);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_52 = lean_box(0);
x_53 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_49, x_42, x_52);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
x_4 = x_12;
x_5 = x_54;
goto _start;
}
}
case 2:
{
lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_10, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_5, 0);
x_60 = lean_ctor_get(x_5, 1);
x_61 = lean_ctor_get(x_5, 2);
x_62 = lean_ctor_get(x_5, 3);
x_63 = l_Lean_Parser_PrattParsingTables_inhabited___closed__1;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_57);
x_65 = l___private_Lean_Parser_Extension_3__addParserCategoryCore(x_61, x_56, x_64);
x_66 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_65, x_6);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_ctor_set(x_5, 2, x_67);
x_4 = x_12;
x_6 = x_68;
goto _start;
}
else
{
uint8_t x_70; 
lean_free_object(x_5);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_12);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
x_76 = lean_ctor_get(x_5, 2);
x_77 = lean_ctor_get(x_5, 3);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_78 = l_Lean_Parser_PrattParsingTables_inhabited___closed__1;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_57);
x_80 = l___private_Lean_Parser_Extension_3__addParserCategoryCore(x_76, x_56, x_79);
x_81 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_80, x_6);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_77);
x_4 = x_12;
x_5 = x_84;
x_6 = x_83;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_12);
lean_dec(x_1);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
default: 
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_10, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_dec(x_10);
x_92 = !lean_is_exclusive(x_5);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 2);
x_96 = lean_ctor_get(x_5, 3);
lean_inc(x_91);
lean_inc(x_95);
lean_inc(x_1);
x_97 = l_Lean_Parser_mkParserOfConstant(x_1, x_95, x_91);
x_98 = l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2(x_97, x_6);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_unbox(x_101);
lean_dec(x_101);
x_104 = l_Lean_Parser_addParser(x_95, x_90, x_91, x_103, x_102);
x_105 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_104, x_100);
lean_dec(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_1);
x_108 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(x_1, x_91, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
lean_ctor_set(x_5, 2, x_106);
x_4 = x_12;
x_6 = x_109;
goto _start;
}
else
{
uint8_t x_111; 
lean_dec(x_106);
lean_free_object(x_5);
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_free_object(x_5);
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_12);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_105);
if (x_115 == 0)
{
return x_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_free_object(x_5);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
return x_98;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_98, 0);
x_121 = lean_ctor_get(x_98, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_98);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_5, 0);
x_124 = lean_ctor_get(x_5, 1);
x_125 = lean_ctor_get(x_5, 2);
x_126 = lean_ctor_get(x_5, 3);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_5);
lean_inc(x_91);
lean_inc(x_125);
lean_inc(x_1);
x_127 = l_Lean_Parser_mkParserOfConstant(x_1, x_125, x_91);
x_128 = l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2(x_127, x_6);
lean_dec(x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_unbox(x_131);
lean_dec(x_131);
x_134 = l_Lean_Parser_addParser(x_125, x_90, x_91, x_133, x_132);
x_135 = l_IO_ofExcept___at___private_Lean_Parser_Extension_4__addBuiltinParserCategory___spec__1(x_134, x_130);
lean_dec(x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_1);
x_138 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(x_1, x_91, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_124);
lean_ctor_set(x_140, 2, x_136);
lean_ctor_set(x_140, 3, x_126);
x_4 = x_12;
x_5 = x_140;
x_6 = x_139;
goto _start;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_136);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_12);
lean_dec(x_1);
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
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
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_91);
lean_dec(x_12);
lean_dec(x_1);
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_148 = x_135;
} else {
 lean_dec_ref(x_135);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_1);
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_152 = x_128;
} else {
 lean_dec_ref(x_128);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_3, x_4);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_14 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__3(x_1, x_10, x_10, x_13, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_4 = x_12;
x_5 = x_15;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_10__ParserExtension_addImported(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Extension_5__ParserExtension_mkInitial(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__4(x_1, x_2, x_2, x_7, x_5, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_10__ParserExtension_addImported___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Parser_Extension_10__ParserExtension_addImported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Extension_10__ParserExtension_addImported(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Parser_ParserExtensionState_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_io_ref_set(x_13, x_24, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_19);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
return x_3;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3(x_18, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
x_23 = lean_io_ref_get(x_3, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_io_ref_reset(x_3, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_io_ref_set(x_3, x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_22);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_27);
lean_dec(x_22);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_22);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_51);
x_54 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_58);
return x_4;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_array_get_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2(x_1, x_59, x_59, x_61, x_62);
lean_dec(x_61);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 5);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_71 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_71, 0, x_65);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3(x_71, x_60);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_69);
x_76 = lean_io_ref_get(x_3, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_75);
x_79 = x_75;
x_80 = lean_array_push(x_77, x_79);
x_81 = lean_io_ref_reset(x_3, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_io_ref_set(x_3, x_80, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_75);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_89 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
lean_dec(x_75);
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_75);
x_95 = lean_ctor_get(x_76, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_76, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_97 = x_76;
} else {
 lean_dec_ref(x_76);
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
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
x_99 = lean_ctor_get(x_72, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_72, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_101 = x_72;
} else {
 lean_dec_ref(x_72);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
lean_dec(x_1);
x_104 = l_Lean_Name_toString___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_103);
x_106 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_108 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_60);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_4);
if (x_112 == 0)
{
return x_4;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_4);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
lean_object* l_Lean_Parser_mkParserExtension___lambda__1(lean_object* x_1) {
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
lean_object* l_Lean_Parser_mkParserExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 0;
x_8 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parserExt");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkParserExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_5__ParserExtension_mkInitial), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_10__ParserExtension_addImported___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_9__ParserExtension_addEntry), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserExtension___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkParserExtension___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_mkParserExtension___closed__2;
x_2 = l_Lean_Parser_mkParserExtension___closed__3;
x_3 = l_Lean_Parser_mkParserExtension___closed__4;
x_4 = l_Lean_Parser_mkParserExtension___closed__5;
x_5 = l_Lean_Parser_mkParserExtension___closed__6;
x_6 = l_Lean_Parser_mkParserExtension___closed__7;
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
lean_object* l_Lean_Parser_mkParserExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_mkParserExtension___closed__8;
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Parser_mkParserExtension___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_mkParserExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserExtension___lambda__2(x_1);
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
x_2 = l_IO_Error_Inhabited___closed__1;
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
lean_object* _init_l_Lean_Parser_parserExtension___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_parserExtension___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__4___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_parserExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_parserExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_parserExtension___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_parserExtension___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_parserExtension___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_parserExtension___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_Parser_parserExtension___closed__2;
x_4 = l_Lean_Parser_parserExtension___closed__3;
x_5 = l_Lean_Parser_parserExtension___closed__4;
x_6 = l_Lean_Parser_parserExtension___closed__5;
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
x_6 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_3__addParserCategoryCore___spec__1(x_5, x_2);
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
x_9 = l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg(x_2);
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
uint8_t l_Lean_Parser_leadingIdentAsSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_parserExtension;
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(x_5, x_2);
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
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean_box(0);
x_5 = 1;
x_6 = l_Lean_Parser_mkAntiquot(x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_addLeadingParser___spec__1(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_9 = l_Lean_Name_toString___closed__1;
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_Parser_mkCategoryAntiquotParser(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Parser_tryAnti(x_2, x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_inc(x_2);
lean_inc(x_17);
x_22 = l_Lean_Parser_leadingParserAux(x_1, x_17, x_18, x_2, x_3);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Parser_trailingLoop___main(x_17, x_2, x_22);
return x_24;
}
else
{
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_2);
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_array_get_size(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_2);
x_28 = lean_apply_2(x_20, x_2, x_3);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_30 = l_Lean_Parser_trailingLoop___main(x_17, x_2, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = lean_nat_dec_eq(x_32, x_27);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_27);
x_34 = l_Lean_Parser_ParserState_restore(x_28, x_26, x_27);
lean_dec(x_26);
lean_inc(x_2);
lean_inc(x_17);
x_35 = l_Lean_Parser_leadingParserAux(x_1, x_17, x_18, x_2, x_34);
x_36 = l_Lean_Parser_mergeOrElseErrors(x_35, x_31, x_27);
lean_dec(x_27);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Parser_trailingLoop___main(x_17, x_2, x_36);
return x_38;
}
else
{
lean_dec(x_37);
lean_dec(x_17);
lean_dec(x_2);
return x_36;
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_setCategoryParserFnRef___closed__1() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_categoryParserFnRef;
x_3 = l_Lean_Parser_setCategoryParserFnRef___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
return x_4;
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
x_6 = l___private_Lean_Parser_Extension_6__addTokenConfig(x_5, x_2);
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
uint8_t l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_Std_PersistentHashMap_containsAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(x_17, x_18, x_3);
lean_dec(x_17);
return x_19;
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
x_5 = l_Std_PersistentHashMap_containsAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(x_3, x_4, x_2);
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
lean_object* l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(x_1, x_4, x_3);
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
x_14 = l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_13, x_4);
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
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_4 = l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_3, x_2);
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
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlMAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_1, x_2);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_getTokenTable(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_3);
return x_5;
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
lean_dec(x_3);
x_8 = l_Lean_Parser_whitespace___main(x_6, x_7);
lean_inc(x_6);
x_9 = l_Lean_Parser_categoryParserFnImpl(x_2, x_6, x_8);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = l_Lean_Parser_ParserState_toErrorMsg(x_6, x_9);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_declareBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_InitAttr_2__isUnitType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_KeyedDeclsAttribute_declareBuiltin___rarg___closed__4;
x_2 = l_Lean_Parser_declareBuiltinParser___closed__4;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin parser '");
return x_1;
}
}
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = l_Lean_Parser_declareBuiltinParser___closed__2;
lean_inc(x_4);
x_7 = l_Lean_Name_append___main(x_6, x_4);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_2, x_8);
x_10 = l_Lean_Name_toExprAux___main(x_3);
lean_inc(x_4);
x_11 = l_Lean_Name_toExprAux___main(x_4);
lean_inc(x_4);
x_12 = l_Lean_mkConst(x_4, x_8);
x_13 = l___private_Lean_Meta_EqnCompiler_CaseArraySizes_2__introArrayLitAux___main___closed__3;
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_11);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_16, x_16, x_17, x_9);
lean_dec(x_16);
x_19 = l_Lean_Parser_declareBuiltinParser___closed__5;
lean_inc(x_7);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_box(0);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Options_empty;
x_26 = l_Lean_Environment_addAndCompile(x_1, x_25, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_7);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_4);
x_29 = l_Lean_Parser_declareBuiltinParser___closed__6;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Char_HasRepr___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_initAttr;
x_37 = lean_box(0);
x_38 = l_Lean_ParametricAttribute_setParam___rarg(x_36, x_35, x_7, x_37);
x_39 = l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(x_38, x_5);
lean_dec(x_38);
return x_39;
}
}
}
lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinLeadingParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTrailingParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`Parser` or `TrailingParser` expected");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_hasArgs(x_5);
if (x_8 == 0)
{
if (x_6 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_registerTagAttribute___lambda__4___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_environment_find(x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = l_Lean_KeyedDeclsAttribute_init___rarg___lambda__3___closed__1;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = l_Lean_ConstantInfo_type(x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 4)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lean_mkAppStx___closed__1;
x_40 = lean_string_dec_eq(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
x_18 = x_41;
goto block_27;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_mkAppStx___closed__3;
x_43 = lean_string_dec_eq(x_37, x_42);
lean_dec(x_37);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_18 = x_44;
goto block_27;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1;
x_46 = lean_string_dec_eq(x_36, x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = lean_string_dec_eq(x_36, x_42);
lean_dec(x_36);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(0);
x_18 = x_48;
goto block_27;
}
else
{
lean_object* x_49; 
lean_inc(x_4);
x_49 = l_Lean_Parser_declareLeadingBuiltinParser(x_3, x_2, x_4, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 1;
x_53 = l_Lean_PrettyPrinter_Parenthesizer_compile(x_50, x_4, x_52, x_51);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_36);
lean_inc(x_4);
x_58 = l_Lean_Parser_declareTrailingBuiltinParser(x_3, x_2, x_4, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = 1;
x_62 = l_Lean_PrettyPrinter_Parenthesizer_compile(x_59, x_4, x_61, x_60);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_18 = x_67;
goto block_27;
}
}
else
{
lean_object* x_68; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_box(0);
x_18 = x_68;
goto block_27;
}
}
else
{
lean_object* x_69; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
x_18 = x_69;
goto block_27;
}
}
else
{
lean_object* x_70; 
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_box(0);
x_18 = x_70;
goto block_27;
}
}
else
{
lean_object* x_71; 
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
x_18 = x_71;
goto block_27;
}
}
block_27:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_4);
x_21 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = l_Lean_Name_toString___closed__1;
x_73 = l_Lean_Name_toStringWithSep___main(x_72, x_1);
x_74 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_7);
return x_79;
}
}
}
lean_object* l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_5);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1() {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___boxed), 7, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_7 = 1;
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_7);
x_9 = l___private_Lean_Parser_Extension_4__addBuiltinParserCategory(x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_registerBuiltinAttribute(x_8, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
lean_object* _init_l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser '");
return x_1;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Parser_addToken(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_1);
x_12 = l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_9);
lean_dec(x_9);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_2 = x_19;
x_3 = x_7;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_Parser_addSyntaxNodeKind(x_4, x_10);
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
x_14 = l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3(x_13, x_4);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Parser_addSyntaxNodeKind(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__4(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__5(x_6, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Parser_Extension_12__ParserAttribute_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_hasArgs(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l_Lean_Parser_parserExtension;
x_10 = l_Lean_PersistentEnvExtension_getState___rarg(x_9, x_3);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_Lean_Parser_mkParserOfConstant(x_3, x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_20, x_21);
lean_inc(x_4);
x_23 = l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1(x_4, x_3, x_22, x_7);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1;
x_29 = lean_apply_1(x_27, x_28);
x_30 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2(x_29, x_25);
lean_dec(x_29);
x_31 = lean_unbox(x_17);
lean_inc(x_18);
lean_inc(x_2);
x_32 = l_Lean_Parser_addParser(x_11, x_2, x_4, x_31, x_18);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_free_object(x_23);
lean_inc(x_4);
x_35 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_4);
lean_ctor_set(x_35, 2, x_18);
x_36 = lean_unbox(x_17);
lean_dec(x_17);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_36);
x_37 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_9, x_30, x_35);
x_38 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(x_37, x_4, x_26);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1;
x_43 = lean_apply_1(x_41, x_42);
x_44 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2(x_43, x_39);
lean_dec(x_43);
x_45 = lean_unbox(x_17);
lean_inc(x_18);
lean_inc(x_2);
x_46 = l_Lean_Parser_addParser(x_11, x_2, x_4, x_45, x_18);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_46);
lean_inc(x_4);
x_50 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_4);
lean_ctor_set(x_50, 2, x_18);
x_51 = lean_unbox(x_17);
lean_dec(x_17);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_51);
x_52 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_9, x_44, x_50);
x_53 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(x_52, x_4, x_40);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_23);
if (x_54 == 0)
{
return x_23;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_23, 0);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = l_Lean_Name_toString___closed__1;
x_59 = l_Lean_Name_toStringWithSep___main(x_58, x_1);
x_60 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Lean_registerTagAttribute___lambda__4___closed__5;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlMAux___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Parser_Extension_12__ParserAttribute_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l___private_Lean_Parser_Extension_12__ParserAttribute_add(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Extension_12__ParserAttribute_add(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___closed__1() {
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_mkParserAttributeImpl___closed__1;
x_5 = 1;
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Parser_mkParserAttributeImpl___elambda__1(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_5);
return x_9;
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
lean_object* _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser attribute implementation builder arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2;
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
x_5 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2;
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
x_12 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_13;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2;
return x_14;
}
}
}
}
lean_object* _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parserAttr");
return x_1;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2;
x_3 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__3;
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
x_7 = l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(x_6, x_5);
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
x_15 = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2;
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
lean_object* _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTermParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinTermParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
x_3 = l_Lean_Parser_termParser___closed__2;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_regTermParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regTermParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regTermParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regTermParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regTermParserAttribute___closed__2;
x_3 = l_Lean_Parser_termParser___closed__2;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Extension(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_mkBuiltinTokenTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
lean_dec_ref(res);
l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef___spec__1);
res = l_Lean_Parser_mkBuiltinSyntaxNodeKindSetRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinSyntaxNodeKindSetRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinSyntaxNodeKindSetRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_1__registerAuxiliaryNodeKindSets(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Parser_mkBuiltinParserCategories___spec__1);
res = l_Lean_Parser_mkBuiltinParserCategories(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinParserCategoriesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinParserCategoriesRef);
lean_dec_ref(res);
l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__1 = _init_l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__1);
l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__2 = _init_l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_2__throwParserCategoryAlreadyDefined___rarg___closed__2);
l_Lean_Parser_ParserExtensionState_inhabited___closed__1 = _init_l_Lean_Parser_ParserExtensionState_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserExtensionState_inhabited___closed__1);
l_Lean_Parser_ParserExtensionState_inhabited = _init_l_Lean_Parser_ParserExtensionState_inhabited();
lean_mark_persistent(l_Lean_Parser_ParserExtensionState_inhabited);
l___private_Lean_Parser_Extension_6__addTokenConfig___closed__1 = _init_l___private_Lean_Parser_Extension_6__addTokenConfig___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_6__addTokenConfig___closed__1);
l___private_Lean_Parser_Extension_6__addTokenConfig___closed__2 = _init_l___private_Lean_Parser_Extension_6__addTokenConfig___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_6__addTokenConfig___closed__2);
l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1 = _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1);
l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1 = _init_l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_8__updateBuiltinTokens___closed__1);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__1 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__2 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__2();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__3 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__3();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__4 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__4();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4);
l_Lean_Parser_compileParserDescr___main___closed__1 = _init_l_Lean_Parser_compileParserDescr___main___closed__1();
lean_mark_persistent(l_Lean_Parser_compileParserDescr___main___closed__1);
l_Lean_Parser_compileParserDescr___main___closed__2 = _init_l_Lean_Parser_compileParserDescr___main___closed__2();
lean_mark_persistent(l_Lean_Parser_compileParserDescr___main___closed__2);
l_Lean_Parser_compileParserDescr___main___closed__3 = _init_l_Lean_Parser_compileParserDescr___main___closed__3();
lean_mark_persistent(l_Lean_Parser_compileParserDescr___main___closed__3);
l_Lean_Parser_compileParserDescr___main___closed__4 = _init_l_Lean_Parser_compileParserDescr___main___closed__4();
lean_mark_persistent(l_Lean_Parser_compileParserDescr___main___closed__4);
l_Lean_Parser_compileParserDescr___main___closed__5 = _init_l_Lean_Parser_compileParserDescr___main___closed__5();
lean_mark_persistent(l_Lean_Parser_compileParserDescr___main___closed__5);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkParserExtension___spec__3___closed__1);
l_Lean_Parser_mkParserExtension___closed__1 = _init_l_Lean_Parser_mkParserExtension___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__1);
l_Lean_Parser_mkParserExtension___closed__2 = _init_l_Lean_Parser_mkParserExtension___closed__2();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__2);
l_Lean_Parser_mkParserExtension___closed__3 = _init_l_Lean_Parser_mkParserExtension___closed__3();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__3);
l_Lean_Parser_mkParserExtension___closed__4 = _init_l_Lean_Parser_mkParserExtension___closed__4();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__4);
l_Lean_Parser_mkParserExtension___closed__5 = _init_l_Lean_Parser_mkParserExtension___closed__5();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__5);
l_Lean_Parser_mkParserExtension___closed__6 = _init_l_Lean_Parser_mkParserExtension___closed__6();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__6);
l_Lean_Parser_mkParserExtension___closed__7 = _init_l_Lean_Parser_mkParserExtension___closed__7();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__7);
l_Lean_Parser_mkParserExtension___closed__8 = _init_l_Lean_Parser_mkParserExtension___closed__8();
lean_mark_persistent(l_Lean_Parser_mkParserExtension___closed__8);
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
l_Lean_Parser_parserExtension___closed__6 = _init_l_Lean_Parser_parserExtension___closed__6();
lean_mark_persistent(l_Lean_Parser_parserExtension___closed__6);
res = l_Lean_Parser_mkParserExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserExtension);
lean_dec_ref(res);
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
l_Lean_Parser_declareBuiltinParser___closed__4 = _init_l_Lean_Parser_declareBuiltinParser___closed__4();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__4);
l_Lean_Parser_declareBuiltinParser___closed__5 = _init_l_Lean_Parser_declareBuiltinParser___closed__5();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__5);
l_Lean_Parser_declareBuiltinParser___closed__6 = _init_l_Lean_Parser_declareBuiltinParser___closed__6();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__6);
l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__1);
l_Lean_Parser_declareLeadingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__2);
l_Lean_Parser_declareTrailingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__1);
l_Lean_Parser_declareTrailingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__2);
l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___closed__1 = _init_l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_11__BuiltinParserAttribute_add___closed__1);
l_Lean_Parser_registerBuiltinParserAttribute___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__1);
l_Lean_Parser_mkParserAttributeImpl___closed__1 = _init_l_Lean_Parser_mkParserAttributeImpl___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserAttributeImpl___closed__1);
l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__1 = _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__1);
l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2 = _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___lambda__1___closed__2);
l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__1 = _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__1);
l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2 = _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__2);
l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__3 = _init_l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder___closed__3);
res = l___private_Lean_Parser_Extension_13__registerParserAttributeImplBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regBuiltinTermParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__1);
l_Lean_Parser_regBuiltinTermParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__2);
res = l_Lean_Parser_regBuiltinTermParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regTermParserAttribute___closed__1 = _init_l_Lean_Parser_regTermParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_regTermParserAttribute___closed__1);
l_Lean_Parser_regTermParserAttribute___closed__2 = _init_l_Lean_Parser_regTermParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_regTermParserAttribute___closed__2);
res = l_Lean_Parser_regTermParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
