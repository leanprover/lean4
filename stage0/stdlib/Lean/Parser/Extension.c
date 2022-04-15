// Lean compiler output
// Module: Lean.Parser.Extension
// Imports: Init Lean.ResolveName Lean.ScopedEnvExtension Lean.Parser.Basic Lean.Parser.StrInterpolation Lean.KeyedDeclsAttribute Lean.DocString Lean.DeclarationRange
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
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_builtinTokenTable;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_810____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__9;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1;
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__4;
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Parser_addToken___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__1;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Parser_addParserTokens___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__4;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__4;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_categoryParserFnRef;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__1;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinParserCategoriesRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_parserExtension;
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_MetavarContext_getExprAssignmentDomain___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_empty(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1;
extern lean_object* l_Lean_declRangeExt;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_getConstAlias___rarg___closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_addLeadingParser___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__11;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFn___closed__5;
static lean_object* l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1;
static lean_object* l_Lean_Parser_isParserCategory___closed__1;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_declareBuiltinParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFn___closed__3;
static lean_object* l_Lean_Parser_mkParserAttributeImpl___closed__2;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkParserState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_evalInsideQuot___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
static lean_object* l_Lean_Parser_getConstAlias___rarg___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__1;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Parser_addToken___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
static lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__1;
size_t lean_uint64_to_usize(uint64_t);
static size_t l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object*);
static lean_object* l_Lean_Parser_parserOfStack___closed__1;
static lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
static lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___closed__1;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Parser_addToken___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
static size_t l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4;
static lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__17;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
static lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_internal_parseQuotWithCurrentStage;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_128_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
static lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__4;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
static lean_object* l_Lean_Parser_categoryParserFnImpl___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_getBinaryAlias___rarg___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__4;
static lean_object* l_Lean_Parser_categoryParserFnImpl___closed__2;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1;
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserContext_resolveName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1932_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3058_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_180_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_74_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_getSyntaxNodeKinds___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_54____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_State_categories___default;
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Internal_isStage0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForAllParserParserAliasValue(lean_object*);
lean_object* l_Lean_Name_toExprAux(lean_object*);
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19;
uint64_t l_Lean_Name_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Parser_addToken___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserFnImpl___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_runParserCategory___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_parserAliasesRef;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__8;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkParserAttributeImpl___closed__1;
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__5;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__3;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__2;
static lean_object* l_Lean_Parser_registerParserAttributeHook___closed__1;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedState___closed__2;
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__5;
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___closed__1;
static uint8_t l_Lean_Parser_isValidSyntaxNodeKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_registerAliasCore___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_insert_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFn___closed__1;
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Parser_runParserAttributeHooks___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_getSyntaxNodeKinds___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_getParserPriority___closed__4;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__3;
static lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__6;
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__6;
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2___boxed(lean_object*);
static lean_object* l_Lean_Parser_registerAliasCore___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_getParserPriority___closed__2;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry;
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_addLeadingParser___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFn___closed__4;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__6;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object*);
static lean_object* l_Lean_Parser_getParserPriority___closed__1;
static lean_object* l_Lean_Parser_getUnaryAlias___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_declareBuiltin___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_ParserExtension_addEntryImpl___spec__1(lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_identKind;
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__3;
static lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Parser_runParserAttributeHooks___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object*);
static lean_object* l_Lean_Parser_registerAlias___closed__1;
lean_object* l_Std_RBNode_find___at_Lean_findDeclarationRanges_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__5;
extern lean_object* l_Lean_scientificLitKind;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg(lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1;
static lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4;
static lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry;
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__1;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__14;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserFnImpl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__5;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1;
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__6;
static lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__3;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__13;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7;
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_parserAttributeHooks;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_State_kinds___default;
extern lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_builtinSyntaxNodeKindSetRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
static lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__8;
static lean_object* l_Lean_Parser_withOpenFn___closed__2;
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__7;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__1;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__1;
lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2(lean_object*);
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2;
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__2;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__5;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__7;
static lean_object* l_Lean_Parser_getConstAlias___rarg___closed__3;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__1;
static lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__2;
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withOpenFn___closed__1;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_State_tokens___default;
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__1;
static lean_object* l_Lean_Parser_getParserPriority___closed__3;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_getParserPriority___closed__5;
static lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__1;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__5;
lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__5;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Parser_addLeadingParser___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
extern lean_object* l_Lean_builtinDeclRanges;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__2;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_find_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_getConstAlias___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForAllParserParserAliasValue__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Parser_registerBuiltinNodeKind___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__1;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__15;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__18;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__2;
lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Trie_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_Parser_registerBuiltinNodeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_Parser_registerBuiltinNodeKind___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_74_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_14 = l_Lean_scientificLitKind;
x_15 = l_Lean_Parser_registerBuiltinNodeKind(x_14, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_charLitKind;
x_18 = l_Lean_Parser_registerBuiltinNodeKind(x_17, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_nameLitKind;
x_21 = l_Lean_Parser_registerBuiltinNodeKind(x_20, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_180_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
x_3 = lean_st_mk_ref(x_2, x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static size_t _init_l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_14 = lean_usize_shift_right(x_2, x_5);
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
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
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
x_16 = lean_box(0);
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
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
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
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
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
x_51 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
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
x_58 = lean_box(0);
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
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
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
x_92 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
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
x_106 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Name_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_2);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_builtinParserCategoriesRef;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2;
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_State_tokens___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_State_kinds___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_State_categories___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState___closed__1() {
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
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedState___closed__1;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedState___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_builtinTokenTable;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Parser_registerBuiltinNodeKind___closed__1;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
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
static lean_object* _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_throwUnknownParserCategory___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_17 = lean_usize_shift_right(x_2, x_5);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Parser_getCategory___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Parser_getCategory___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Parser_addLeadingParser___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_box(0);
x_8 = lean_name_mk_string(x_7, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_name_mk_string(x_12, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_addLeadingParser___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_addLeadingParser___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_List_mapTRAux___at_Lean_Parser_addLeadingParser___spec__1(x_11, x_12);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_13);
x_17 = l_List_foldl___at_Lean_Parser_addLeadingParser___spec__2(x_4, x_5, x_15, x_16);
lean_ctor_set(x_10, 0, x_17);
x_18 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_20);
lean_dec(x_10);
x_22 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_13);
x_23 = l_List_foldl___at_Lean_Parser_addLeadingParser___spec__2(x_4, x_5, x_20, x_22);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_21);
x_25 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_box(0);
x_30 = l_List_mapTRAux___at_Lean_Parser_addLeadingParser___spec__1(x_28, x_29);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_30);
x_34 = l_List_foldl___at_Lean_Parser_addLeadingParser___spec__3(x_4, x_5, x_32, x_33);
lean_ctor_set(x_27, 0, x_34);
x_35 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_27);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_inc(x_37);
lean_dec(x_27);
x_39 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_30);
x_40 = l_List_foldl___at_Lean_Parser_addLeadingParser___spec__3(x_4, x_5, x_37, x_39);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_38);
x_42 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
default: 
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_9);
x_44 = lean_ctor_get(x_6, 0);
lean_inc(x_44);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 3);
lean_inc(x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_5);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_46, 1);
x_53 = lean_ctor_get(x_46, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_46, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_46, 0);
lean_dec(x_55);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_46, 1, x_56);
x_57 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_44);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_49);
lean_ctor_set(x_44, 0, x_61);
x_62 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_44);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 3);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_5);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 4, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_67);
lean_ctor_set(x_73, 3, x_68);
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_65);
x_75 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_1, x_2, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_addLeadingParser(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTRAux___at_Lean_Parser_addLeadingParser___spec__1(x_6, x_7);
x_9 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_8);
x_10 = l_List_foldl___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__1(x_2, x_3, x_1, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = l_List_mapTRAux___at_Lean_Parser_addLeadingParser___spec__1(x_11, x_12);
x_14 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_13);
x_15 = l_List_foldl___at___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux___spec__2(x_2, x_3, x_1, x_14);
return x_15;
}
default: 
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_1, 3, x_19);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Parser_addParserTokens___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
x_6 = l_List_foldlM___at_Lean_Parser_addParserTokens___spec__1(x_1, x_5);
return x_6;
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1;
x_5 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1;
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = l_Lean_Name_toString(x_2, x_12);
x_14 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
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
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_2, x_32);
x_34 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_31);
lean_dec(x_31);
x_39 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_ParserExtension_addEntryImpl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.Extension");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.ParserExtension.addEntryImpl");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__1;
x_2 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__2;
x_3 = lean_unsigned_to_nat(155u);
x_4 = lean_unsigned_to_nat(26u);
x_5 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__1;
x_2 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__2;
x_3 = lean_unsigned_to_nat(165u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_5, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
x_9 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__4;
x_10 = l_panic___at_Lean_Parser_ParserExtension_addEntryImpl___spec__1(x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_12, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_16 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__4;
x_17 = l_panic___at_Lean_Parser_ParserExtension_addEntryImpl___spec__1(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
return x_19;
}
}
}
case 1:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_box(0);
x_24 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_22, x_20, x_23);
lean_ctor_set(x_1, 1, x_24);
return x_1;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_26, x_20, x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
return x_30;
}
}
case 2:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_inc(x_31);
lean_inc(x_35);
x_36 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_35, x_31);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_1, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
x_41 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_32);
x_43 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_35, x_31, x_42);
lean_ctor_set(x_1, 2, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_44 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_32);
x_46 = l_Std_PersistentHashMap_insert___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__4(x_35, x_31, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_46);
return x_47;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
return x_1;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 3);
lean_inc(x_52);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
x_56 = lean_ctor_get(x_1, 2);
x_57 = l_Lean_Parser_addParser(x_56, x_48, x_49, x_50, x_51, x_52);
lean_dec(x_49);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_57);
lean_free_object(x_1);
lean_dec(x_55);
lean_dec(x_54);
x_58 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__5;
x_59 = l_panic___at_Lean_Parser_ParserExtension_addEntryImpl___spec__1(x_58);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_1, 2, x_60);
return x_1;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_1, 1);
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_1);
x_64 = l_Lean_Parser_addParser(x_63, x_48, x_49, x_50, x_51, x_52);
lean_dec(x_49);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_65 = l_Lean_Parser_ParserExtension_addEntryImpl___closed__5;
x_66 = l_panic___at_Lean_Parser_ParserExtension_addEntryImpl___spec__1(x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_67);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_2, x_3);
x_10 = lean_st_ref_set(x_1, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alias '");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_6 = lean_st_ref_get(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_NameMap_contains___rarg(x_8, x_2);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_Parser_registerAliasCore___rarg___lambda__1(x_1, x_2, x_3, x_11, x_9);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_2, x_13);
x_15 = l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = l_Lean_NameMap_contains___rarg(x_20, x_2);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Parser_registerAliasCore___rarg___lambda__1(x_1, x_2, x_3, x_23, x_21);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_25 = 1;
x_26 = l_Lean_Name_toString(x_2, x_25);
x_27 = l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("aliases can only be registered during initialization");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_registerAliasCore___rarg___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_io_initializing(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = l_Lean_Parser_registerAliasCore___rarg___closed__2;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_Parser_registerAliasCore___rarg___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_registerAliasCore___rarg___lambda__2(x_1, x_2, x_3, x_15, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_registerAliasCore___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_registerAliasCore___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_registerAliasCore___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg(x_6, x_2);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg(x_8, x_2);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_getAlias___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_getAlias___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_getAlias___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_getConstAlias___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser '");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_getConstAlias___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was not found");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_getConstAlias___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a constant, it takes one argument");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_getConstAlias___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a constant, it takes two arguments");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_getAlias___rarg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_2, x_8);
x_10 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Parser_getConstAlias___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_2, x_16);
x_18 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Parser_getConstAlias___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
switch (lean_obj_tag(x_24)) {
case 0:
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
case 1:
{
uint8_t x_31; 
lean_dec(x_24);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = 1;
x_34 = l_Lean_Name_toString(x_2, x_33);
x_35 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Parser_getConstAlias___rarg___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = 1;
x_42 = l_Lean_Name_toString(x_2, x_41);
x_43 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_Lean_Parser_getConstAlias___rarg___closed__3;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
default: 
{
uint8_t x_49; 
lean_dec(x_24);
x_49 = !lean_is_exclusive(x_4);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_4, 0);
lean_dec(x_50);
x_51 = 1;
x_52 = l_Lean_Name_toString(x_2, x_51);
x_53 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lean_Parser_getConstAlias___rarg___closed__4;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_57);
return x_4;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_4, 1);
lean_inc(x_58);
lean_dec(x_4);
x_59 = 1;
x_60 = l_Lean_Name_toString(x_2, x_59);
x_61 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lean_Parser_getConstAlias___rarg___closed__4;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_getConstAlias___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_getConstAlias___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_getUnaryAlias___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not take one argument");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_getAlias___rarg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_2, x_8);
x_10 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Parser_getConstAlias___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_2, x_16);
x_18 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Parser_getConstAlias___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 1)
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_24);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = 1;
x_34 = l_Lean_Name_toString(x_2, x_33);
x_35 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Parser_getUnaryAlias___rarg___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = 1;
x_42 = l_Lean_Name_toString(x_2, x_41);
x_43 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_Lean_Parser_getUnaryAlias___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_getUnaryAlias___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_getUnaryAlias___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_getBinaryAlias___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not take two arguments");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_getAlias___rarg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_2, x_8);
x_10 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Parser_getConstAlias___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_2, x_16);
x_18 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Parser_getConstAlias___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 2)
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_24);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = 1;
x_34 = l_Lean_Name_toString(x_2, x_33);
x_35 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Parser_getBinaryAlias___rarg___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_39);
return x_4;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = 1;
x_42 = l_Lean_Name_toString(x_2, x_41);
x_43 = l_Lean_Parser_getConstAlias___rarg___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_Lean_Parser_getBinaryAlias___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_getBinaryAlias___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_getBinaryAlias___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1932_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_Parser_registerAlias___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_parserAliasesRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_registerAlias___closed__1;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForAllParserParserAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForAllParserParserAliasValue__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_registerAlias___closed__1;
x_4 = l_Lean_Parser_getAlias___rarg(x_3, x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 0;
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_isParserAlias(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_registerAlias___closed__1;
x_4 = l_Lean_Parser_getUnaryAlias___rarg(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_registerAlias___closed__1;
x_4 = l_Lean_Parser_getBinaryAlias___rarg(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_registerAlias___closed__1;
x_4 = l_Lean_Parser_getConstAlias___rarg(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parser type at '");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected)");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserDescr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParserDescr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_1, x_8);
x_10 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Lean_ConstantInfo_type(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
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
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
x_24 = lean_string_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = 1;
x_26 = l_Lean_Name_toString(x_1, x_25);
x_27 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
x_34 = lean_string_dec_eq(x_21, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__6;
x_36 = lean_string_dec_eq(x_21, x_35);
lean_dec(x_21);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_37 = 1;
x_38 = l_Lean_Name_toString(x_1, x_37);
x_39 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_4);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_eval_const(x_5, x_6, x_1);
lean_dec(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_46 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__1(x_45, x_4);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_apply_3(x_2, x_47, x_3, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
return x_49;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_49, 0);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_49);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
return x_46;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_46, 0);
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_21);
x_69 = lean_eval_const(x_5, x_6, x_1);
lean_dec(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_70 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__2(x_69, x_4);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_apply_3(x_2, x_71, x_3, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = 1;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_73, 0, x_78);
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
x_81 = 1;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_73);
if (x_85 == 0)
{
return x_73;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_73, 0);
x_87 = lean_ctor_get(x_73, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_73);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_70);
if (x_89 == 0)
{
return x_70;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_70, 0);
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_70);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
case 1:
{
lean_object* x_93; 
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_ctor_get(x_20, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_18, 1);
lean_inc(x_94);
lean_dec(x_18);
x_95 = lean_ctor_get(x_19, 1);
lean_inc(x_95);
lean_dec(x_19);
x_96 = lean_ctor_get(x_20, 1);
lean_inc(x_96);
lean_dec(x_20);
x_97 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
x_98 = lean_string_dec_eq(x_96, x_97);
lean_dec(x_96);
if (x_98 == 0)
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_5);
x_99 = 1;
x_100 = l_Lean_Name_toString(x_1, x_99);
x_101 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_4);
return x_106;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__7;
x_108 = lean_string_dec_eq(x_95, x_107);
lean_dec(x_95);
if (x_108 == 0)
{
uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_5);
x_109 = 1;
x_110 = l_Lean_Name_toString(x_1, x_109);
x_111 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_4);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__8;
x_118 = lean_string_dec_eq(x_94, x_117);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = lean_string_dec_eq(x_94, x_107);
lean_dec(x_94);
if (x_119 == 0)
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_6);
lean_dec(x_5);
x_120 = 1;
x_121 = l_Lean_Name_toString(x_1, x_120);
x_122 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_4);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_eval_const(x_5, x_6, x_1);
lean_dec(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_129 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3(x_128, x_4);
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = 1;
x_133 = lean_box(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_129, 0, x_134);
return x_129;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_129, 0);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_129);
x_137 = 1;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_135);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_129);
if (x_141 == 0)
{
return x_129;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_129, 0);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_129);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_94);
x_145 = lean_eval_const(x_5, x_6, x_1);
lean_dec(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_146 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3(x_145, x_4);
lean_dec(x_145);
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = 0;
x_150 = lean_box(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set(x_146, 0, x_151);
return x_146;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_146, 0);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_146);
x_154 = 0;
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_153);
return x_157;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_146);
if (x_158 == 0)
{
return x_146;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_146, 0);
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_146);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
}
}
else
{
uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
x_162 = 1;
x_163 = l_Lean_Name_toString(x_1, x_162);
x_164 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_165 = lean_string_append(x_164, x_163);
lean_dec(x_163);
x_166 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_167 = lean_string_append(x_165, x_166);
x_168 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_4);
return x_169;
}
}
default: 
{
uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_170 = 1;
x_171 = l_Lean_Name_toString(x_1, x_170);
x_172 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_173 = lean_string_append(x_172, x_171);
lean_dec(x_171);
x_174 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_4);
return x_177;
}
}
}
else
{
uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_178 = 1;
x_179 = l_Lean_Name_toString(x_1, x_178);
x_180 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_181 = lean_string_append(x_180, x_179);
lean_dec(x_179);
x_182 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_183 = lean_string_append(x_181, x_182);
x_184 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_4);
return x_185;
}
}
else
{
uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_186 = 1;
x_187 = l_Lean_Name_toString(x_1, x_186);
x_188 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_4);
return x_193;
}
}
else
{
uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_194 = 1;
x_195 = l_Lean_Name_toString(x_1, x_194);
x_196 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_197 = lean_string_append(x_196, x_195);
lean_dec(x_195);
x_198 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__3;
x_199 = lean_string_append(x_197, x_198);
x_200 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_4);
return x_201;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_4 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
lean_inc(x_2);
x_7 = l_Lean_Parser_symbolFnAux(x_1, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_string_utf8_get(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = 37;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_tokenAntiquotFn(x_2, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_4 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
lean_inc(x_2);
x_7 = l_Lean_Parser_nonReservedSymbolFnAux(x_1, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_string_utf8_get(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = 37;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_tokenAntiquotFn(x_2, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Parser_registerAlias___closed__1;
x_7 = l_Lean_Parser_getConstAlias___rarg(x_6, x_5, x_4);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Parser_registerAlias___closed__1;
x_11 = l_Lean_Parser_getUnaryAlias___rarg(x_10, x_8, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Parser_compileParserDescr_visit(x_1, x_9, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_apply_1(x_12, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_apply_1(x_12, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
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
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_Parser_registerAlias___closed__1;
x_34 = l_Lean_Parser_getBinaryAlias___rarg(x_33, x_30, x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_3);
lean_inc(x_1);
x_37 = l_Lean_Parser_compileParserDescr_visit(x_1, x_31, x_3, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Parser_compileParserDescr_visit(x_1, x_32, x_3, x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_apply_2(x_35, x_38, x_42);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_apply_2(x_35, x_38, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_38);
lean_dec(x_35);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_34);
if (x_56 == 0)
{
return x_34;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 3:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 2);
lean_inc(x_62);
lean_dec(x_2);
x_63 = l_Lean_Parser_compileParserDescr_visit(x_1, x_62, x_3, x_4);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_61);
x_66 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_66, 0, x_61);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_inc(x_60);
x_68 = l_Lean_Parser_nodeInfo(x_60, x_67);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_70, 0, x_60);
lean_closure_set(x_70, 1, x_69);
x_71 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_71, 0, x_61);
x_72 = l_Lean_Parser_epsilonInfo;
x_73 = l_Lean_Parser_andthenInfo(x_68, x_72);
x_74 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_74, 0, x_70);
lean_closure_set(x_74, 1, x_71);
x_75 = l_Lean_Parser_andthenInfo(x_72, x_73);
x_76 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_76, 0, x_66);
lean_closure_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_63, 0, x_77);
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
lean_inc(x_61);
x_80 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_80, 0, x_61);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_inc(x_60);
x_82 = l_Lean_Parser_nodeInfo(x_60, x_81);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_84, 0, x_60);
lean_closure_set(x_84, 1, x_83);
x_85 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_85, 0, x_61);
x_86 = l_Lean_Parser_epsilonInfo;
x_87 = l_Lean_Parser_andthenInfo(x_82, x_86);
x_88 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_88, 0, x_84);
lean_closure_set(x_88, 1, x_85);
x_89 = l_Lean_Parser_andthenInfo(x_86, x_87);
x_90 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_90, 0, x_80);
lean_closure_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_79);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_61);
lean_dec(x_60);
x_93 = !lean_is_exclusive(x_63);
if (x_93 == 0)
{
return x_63;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_63, 0);
x_95 = lean_ctor_get(x_63, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_63);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
case 4:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
x_101 = l_Lean_Parser_compileParserDescr_visit(x_1, x_100, x_3, x_4);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_98);
x_104 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_104, 0, x_98);
x_105 = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_105, 0, x_99);
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_inc(x_97);
x_107 = l_Lean_Parser_nodeInfo(x_97, x_106);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_109, 0, x_97);
lean_closure_set(x_109, 1, x_108);
x_110 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_110, 0, x_98);
x_111 = l_Lean_Parser_epsilonInfo;
x_112 = l_Lean_Parser_andthenInfo(x_107, x_111);
x_113 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_113, 0, x_109);
lean_closure_set(x_113, 1, x_110);
x_114 = l_Lean_Parser_andthenInfo(x_111, x_112);
x_115 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_115, 0, x_105);
lean_closure_set(x_115, 1, x_113);
x_116 = l_Lean_Parser_andthenInfo(x_111, x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_117, 0, x_104);
lean_closure_set(x_117, 1, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_101, 0, x_118);
return x_101;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_119 = lean_ctor_get(x_101, 0);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_101);
lean_inc(x_98);
x_121 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_121, 0, x_98);
x_122 = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_122, 0, x_99);
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
lean_inc(x_97);
x_124 = l_Lean_Parser_nodeInfo(x_97, x_123);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_dec(x_119);
x_126 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_126, 0, x_97);
lean_closure_set(x_126, 1, x_125);
x_127 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_127, 0, x_98);
x_128 = l_Lean_Parser_epsilonInfo;
x_129 = l_Lean_Parser_andthenInfo(x_124, x_128);
x_130 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_130, 0, x_126);
lean_closure_set(x_130, 1, x_127);
x_131 = l_Lean_Parser_andthenInfo(x_128, x_129);
x_132 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_132, 0, x_122);
lean_closure_set(x_132, 1, x_130);
x_133 = l_Lean_Parser_andthenInfo(x_128, x_131);
x_134 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_134, 0, x_121);
lean_closure_set(x_134, 1, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_120);
return x_136;
}
}
else
{
uint8_t x_137; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_137 = !lean_is_exclusive(x_101);
if (x_137 == 0)
{
return x_101;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_101, 0);
x_139 = lean_ctor_get(x_101, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_101);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
case 5:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_ctor_get(x_2, 0);
lean_inc(x_141);
lean_dec(x_2);
x_142 = l_String_trim(x_141);
lean_dec(x_141);
lean_inc(x_142);
x_143 = l_Lean_Parser_symbolInfo(x_142);
x_144 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit___lambda__1___boxed), 3, 1);
lean_closure_set(x_144, 0, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_4);
return x_146;
}
case 6:
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_3);
lean_dec(x_1);
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_149 = l_String_trim(x_147);
lean_dec(x_147);
lean_inc(x_149);
x_150 = l_Lean_Parser_nonReservedSymbolInfo(x_149, x_148);
x_151 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit___lambda__2), 3, 1);
lean_closure_set(x_151, 0, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_4);
return x_153;
}
case 7:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_3);
x_154 = lean_ctor_get(x_2, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 1);
lean_inc(x_155);
lean_dec(x_2);
lean_inc(x_154);
x_156 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_1, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_155);
x_157 = l_Lean_Parser_throwUnknownParserCategory___rarg(x_154);
x_158 = l_IO_ofExcept___at_Lean_Parser_mkParserOfConstantUnsafe___spec__3(x_157, x_4);
lean_dec(x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_156);
x_159 = l_Lean_Parser_categoryParser(x_154, x_155);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_4);
return x_160;
}
}
case 8:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_2, 0);
lean_inc(x_161);
lean_dec(x_2);
x_162 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr_visit), 4, 1);
lean_closure_set(x_162, 0, x_1);
x_163 = l_Lean_Parser_mkParserOfConstantUnsafe(x_161, x_162, x_3, x_4);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_163);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
return x_163;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_163, 0);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_163);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
case 9:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_2, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_2, 2);
lean_inc(x_177);
lean_dec(x_2);
x_178 = l_Lean_Parser_compileParserDescr_visit(x_1, x_177, x_3, x_4);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_178, 0);
x_181 = 1;
x_182 = l_Lean_Parser_nodeWithAntiquot(x_175, x_176, x_180, x_181);
lean_dec(x_175);
lean_ctor_set(x_178, 0, x_182);
return x_178;
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_178, 0);
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_178);
x_185 = 1;
x_186 = l_Lean_Parser_nodeWithAntiquot(x_175, x_176, x_183, x_185);
lean_dec(x_175);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
}
else
{
uint8_t x_188; 
lean_dec(x_176);
lean_dec(x_175);
x_188 = !lean_is_exclusive(x_178);
if (x_188 == 0)
{
return x_178;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_178, 0);
x_190 = lean_ctor_get(x_178, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_178);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 10:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_2, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_2, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_2, 2);
lean_inc(x_194);
x_195 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_196 = l_Lean_Parser_compileParserDescr_visit(x_1, x_192, x_3, x_4);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Parser_compileParserDescr_visit(x_1, x_194, x_3, x_198);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = l_Lean_Parser_sepBy(x_197, x_193, x_201, x_195);
lean_dec(x_193);
lean_ctor_set(x_199, 0, x_202);
return x_199;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_199, 0);
x_204 = lean_ctor_get(x_199, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_199);
x_205 = l_Lean_Parser_sepBy(x_197, x_193, x_203, x_195);
lean_dec(x_193);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
uint8_t x_207; 
lean_dec(x_197);
lean_dec(x_193);
x_207 = !lean_is_exclusive(x_199);
if (x_207 == 0)
{
return x_199;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_199, 0);
x_209 = lean_ctor_get(x_199, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_199);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_3);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_196);
if (x_211 == 0)
{
return x_196;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_196, 0);
x_213 = lean_ctor_get(x_196, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_196);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
default: 
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_2, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_2, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_2, 2);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_219 = l_Lean_Parser_compileParserDescr_visit(x_1, x_215, x_3, x_4);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = l_Lean_Parser_compileParserDescr_visit(x_1, x_217, x_3, x_221);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = l_Lean_Parser_sepBy1(x_220, x_216, x_224, x_218);
lean_dec(x_216);
lean_ctor_set(x_222, 0, x_225);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_222, 0);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_222);
x_228 = l_Lean_Parser_sepBy1(x_220, x_216, x_226, x_218);
lean_dec(x_216);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_220);
lean_dec(x_216);
x_230 = !lean_is_exclusive(x_222);
if (x_230 == 0)
{
return x_222;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_222, 0);
x_232 = lean_ctor_get(x_222, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_222);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_3);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_219);
if (x_234 == 0)
{
return x_219;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_219, 0);
x_236 = lean_ctor_get(x_219, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_219);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_compileParserDescr_visit___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_compileParserDescr_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_compileParserDescr), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Parser_mkParserOfConstantUnsafe(x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3058_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_Parser_registerParserAttributeHook___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_parserAttributeHooks;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_Lean_Parser_registerParserAttributeHook___closed__1;
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
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Parser_runParserAttributeHooks___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_box(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_apply_6(x_10, x_1, x_2, x_12, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_4 = x_11;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Parser_registerParserAttributeHook___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_forM___at_Lean_Parser_runParserAttributeHooks___spec__1(x_1, x_2, x_3, x_11, x_4, x_5, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Parser_runParserAttributeHooks___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_List_forM___at_Lean_Parser_runParserAttributeHooks___spec__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = 1;
x_11 = l_Lean_Parser_runParserAttributeHooks(x_9, x_1, x_10, x_4, x_5, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attribute cannot be erased");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runBuiltinParserAttributeHooks");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitly run hooks normally activated by builtin parser attributes");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__3;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__4;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__5;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__7;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = 0;
x_11 = l_Lean_Parser_runParserAttributeHooks(x_9, x_1, x_10, x_4, x_5, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runParserAttributeHooks");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitly run hooks normally activated by parser attributes");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__3;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__4;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__5;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__6;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_13 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_16);
x_19 = l_Lean_Parser_mkParserOfConstant(x_18, x_16, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_17);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_25);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_17);
x_31 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
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
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parserExt");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ParserExtension_Entry_toOLeanEntry___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ParserExtension_addEntryImpl), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__3;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__4;
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__5;
x_5 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__6;
x_6 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7;
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__8;
x_3 = l_Lean_registerScopedEnvExtensionUnsafe___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_isParserCategory___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_parserExtension;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_4 = l_Lean_Parser_isParserCategory___closed__1;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_PersistentHashMap_contains___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isParserCategory(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_2);
x_4 = l_Lean_Parser_isParserCategory(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_3);
x_6 = l_Lean_Parser_isParserCategory___closed__1;
x_7 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_6, x_1, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_addParserCategory(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_4 = l_Lean_Parser_isParserCategory___closed__1;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_6, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_leadingIdentBehavior(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_8 = l_Lean_Parser_isParserCategory___closed__1;
x_9 = l_Lean_ScopedEnvExtension_getState___rarg(x_7, x_8, x_5);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Parser_mkParserOfConstant(x_10, x_1, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_io_error_to_string(x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_19, x_20);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parseQuotWithCurrentStage");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(Lean bootstrapping) use parsers from the current stage inside quotations");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__4;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_54____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_evalInsideQuot___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_internal_parseQuotWithCurrentStage;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 4);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_8, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_evalInsideQuot___elambda__1___closed__1;
x_14 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_2(x_15, x_3, x_4);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_1);
x_18 = l_Lean_Environment_contains(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_2(x_19, x_3, x_4);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = l_Lean_Parser_evalParserConstUnsafe(x_1, x_3, x_4);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_2(x_22, x_3, x_4);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___elambda__1), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_4);
return x_2;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_4);
lean_inc(x_2);
x_7 = l_Lean_Parser_evalInsideQuot(x_2, x_4);
x_8 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1;
x_9 = lean_st_ref_get(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Parser_addParser(x_10, x_1, x_2, x_3, x_7, x_5);
x_13 = l_IO_ofExcept___at___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___spec__1(x_12, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_set(x_8, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lean_Parser_registerBuiltinNodeKind___closed__1;
x_21 = lean_st_ref_take(x_20, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_1(x_19, x_22);
x_25 = lean_st_ref_set(x_20, x_24, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(x_18, x_2, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Parser_addBuiltinParser(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Parser_mkAntiquot(x_3, x_4, x_2);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_mkCategoryAntiquotParser(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lean_Parser_categoryParserFnImpl___closed__2;
x_5 = lean_name_eq(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_9 = l_Lean_Parser_isParserCategory___closed__1;
x_10 = l_Lean_ScopedEnvExtension_getState___rarg(x_8, x_9, x_7);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
if (x_5 == 0)
{
x_12 = x_1;
goto block_44;
}
else
{
lean_object* x_45; 
lean_dec(x_1);
x_45 = l_Lean_Parser_categoryParserFnImpl___closed__4;
x_12 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_13; 
lean_inc(x_12);
x_13 = l_Std_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_12, x_14);
x_16 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint32_t x_32; uint8_t x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
lean_dec(x_22);
lean_inc(x_12);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn), 3, 1);
lean_closure_set(x_25, 0, x_12);
x_26 = lean_box(x_24);
lean_inc(x_23);
lean_inc(x_12);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(x_27, 0, x_12);
lean_closure_set(x_27, 1, x_23);
lean_closure_set(x_27, 2, x_26);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_string_utf8_get(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = 36;
x_33 = lean_uint32_dec_eq(x_31, x_32);
x_34 = lean_box(0);
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_27);
lean_dec(x_25);
lean_inc(x_2);
lean_inc(x_23);
x_35 = l_Lean_Parser_leadingParserAux(x_12, x_23, x_24, x_2, x_3);
x_36 = lean_ctor_get(x_35, 4);
lean_inc(x_36);
x_37 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_810____at_Lean_Parser_ParserState_hasError___spec__1(x_36, x_34);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_23);
lean_dec(x_2);
return x_35;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Parser_trailingLoop(x_23, x_2, x_35);
return x_38;
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_12);
x_39 = 1;
lean_inc(x_2);
x_40 = l_Lean_Parser_orelseFnCore(x_25, x_27, x_39, x_2, x_3);
x_41 = lean_ctor_get(x_40, 4);
lean_inc(x_41);
x_42 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_810____at_Lean_Parser_ParserState_hasError___spec__1(x_41, x_34);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_23);
lean_dec(x_2);
return x_40;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Parser_trailingLoop(x_23, x_2, x_40);
return x_43;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_categoryParserFnRef;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__1;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__2;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Parser_addToken___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 3);
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
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Parser_addToken___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___at_Lean_Parser_addToken___spec__2(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_11, x_2);
x_14 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
lean_ctor_set(x_8, 4, x_14);
lean_ctor_set(x_8, 0, x_13);
x_15 = lean_st_ref_set(x_5, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
x_24 = lean_ctor_get(x_8, 2);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_26 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_22, x_2);
x_27 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_st_ref_set(x_5, x_28, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_4);
x_34 = lean_st_ref_take(x_5, x_6);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 4);
lean_dec(x_39);
x_40 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_38, x_2);
x_41 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
lean_ctor_set(x_35, 4, x_41);
lean_ctor_set(x_35, 0, x_40);
x_42 = lean_st_ref_set(x_5, x_35, x_36);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
x_51 = lean_ctor_get(x_35, 2);
x_52 = lean_ctor_get(x_35, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_53 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_49, x_2);
x_54 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_54);
x_56 = lean_st_ref_set(x_5, x_55, x_36);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
default: 
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_4, 4);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_st_ref_take(x_5, x_6);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 4);
lean_dec(x_67);
x_68 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_66, x_61, x_2);
x_69 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
lean_ctor_set(x_63, 4, x_69);
lean_ctor_set(x_63, 0, x_68);
x_70 = lean_st_ref_set(x_5, x_63, x_64);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_63, 0);
x_78 = lean_ctor_get(x_63, 1);
x_79 = lean_ctor_get(x_63, 2);
x_80 = lean_ctor_get(x_63, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_81 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_77, x_61, x_2);
x_82 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_80);
lean_ctor_set(x_83, 4, x_82);
x_84 = lean_st_ref_set(x_5, x_83, x_64);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_11 = l_Lean_Parser_isParserCategory___closed__1;
x_12 = l_Lean_ScopedEnvExtension_getState___rarg(x_10, x_11, x_9);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(x_13, x_1);
x_15 = l_Lean_ofExcept___at_Lean_Parser_addToken___spec__1(x_14, x_3, x_4, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3(x_11, x_17, x_2, x_3, x_4, x_16);
lean_dec(x_4);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Parser_addToken___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Parser_addToken___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Parser_addToken___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_Parser_addToken___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_addToken(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_isParserCategory___closed__1;
x_5 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_14 = lean_usize_shift_right(x_2, x_5);
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
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = LEAN_IS_STAGE0;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_4 = l_Lean_Parser_isParserCategory___closed__1;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_2);
x_7 = l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Parser_isValidSyntaxNodeKind___closed__1;
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_Environment_contains(x_1, x_2);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Parser_isValidSyntaxNodeKind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isValidSyntaxNodeKind(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_getSyntaxNodeKinds___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_12, x_4);
x_2 = x_8;
x_4 = x_13;
goto _start;
}
default: 
{
x_2 = x_8;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_getSyntaxNodeKinds___spec__3(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___closed__1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_MetavarContext_getExprAssignmentDomain___spec__4___rarg(x_13, x_11, x_12, lean_box(0), x_14, x_2);
lean_dec(x_12);
lean_dec(x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_3 = l_Lean_Parser_isParserCategory___closed__1;
x_4 = l_Lean_ScopedEnvExtension_getState___rarg(x_2, x_3, x_1);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Std_PersistentHashMap_foldlM___at_Lean_Parser_getSyntaxNodeKinds___spec__1(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_getSyntaxNodeKinds___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_getSyntaxNodeKinds___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_3 = l_Lean_Parser_isParserCategory___closed__1;
x_4 = l_Lean_ScopedEnvExtension_getState___rarg(x_2, x_3, x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_getTokenTable(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_getTokenTable(x_3);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_5);
lean_ctor_set(x_8, 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_mkParserState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Parser_mkParserState___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_runParserCategory___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end of input");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_3);
x_5 = l_Lean_Parser_mkInputContext(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
x_9 = l_Lean_Parser_mkParserContext(x_5, x_8);
x_10 = l_Lean_Parser_mkParserState(x_3);
x_11 = l_Lean_Parser_whitespace(x_9, x_10);
lean_inc(x_9);
x_12 = l_Lean_Parser_categoryParserFnImpl(x_2, x_9, x_11);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
x_14 = lean_box(0);
x_15 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_810____at_Lean_Parser_ParserState_hasError___spec__1(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = l_Lean_Parser_ParserState_toErrorMsg(x_9, x_12);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
x_19 = lean_string_utf8_at_end(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Parser_runParserCategory___closed__1;
x_21 = l_Lean_Parser_ParserState_mkError(x_12, x_20);
x_22 = l_Lean_Parser_ParserState_toErrorMsg(x_9, x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
x_25 = l_Lean_instInhabitedSyntax;
x_26 = l_Array_back___rarg(x_25, x_24);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_1, x_8);
x_10 = l_Lean_Name_toExprAux(x_2);
lean_inc(x_3);
x_11 = l_Lean_Name_toExprAux(x_3);
lean_inc(x_3);
x_12 = l_Lean_mkConst(x_3, x_8);
x_13 = l_Lean_mkRawNatLit(x_4);
x_14 = l_Lean_Parser_declareBuiltinParser___closed__1;
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = l_Lean_mkAppN(x_9, x_18);
x_20 = l_Lean_declareBuiltin(x_3, x_19, x_5, x_6, x_7);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinLeadingParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
x_2 = l_Lean_Parser_declareLeadingBuiltinParser___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_declareLeadingBuiltinParser___closed__4;
x_8 = l_Lean_Parser_declareBuiltinParser(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
x_2 = l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
x_8 = l_Lean_Parser_declareBuiltinParser(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
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
x_7 = l_Lean_Parser_getParserPriority___closed__2;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Syntax_getArg(x_1, x_3);
x_9 = l_Lean_numLitKind;
x_10 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_9, x_8);
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
x_14 = l_Lean_Parser_getParserPriority___closed__5;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_getParserPriority(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_isRecCore(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_isRecCore(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
static lean_object* _init_l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_declRangeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_instInhabitedDeclarationRanges;
x_10 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1;
x_11 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_9, x_10, x_8, x_1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instInhabitedDeclarationRanges;
x_16 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1;
x_17 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_15, x_16, x_14, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_builtinDeclRanges;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___closed__1;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Std_RBNode_find___at_Lean_findDeclarationRanges_x3f___spec__1(x_11, x_1);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Std_RBNode_find___at_Lean_findDeclarationRanges_x3f___spec__1(x_13, x_1);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lean_isRec___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__2(x_1, x_2, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_8);
x_12 = lean_is_aux_recursor(x_8, x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___closed__1;
lean_inc(x_1);
x_14 = l_Lean_TagDeclarationExtension_isTagged(x_13, x_8, x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_unbox(x_10);
lean_dec(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_16 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(x_1, x_2, x_3, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(x_1, x_17, x_2, x_3, x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_Name_getPrefix(x_1);
x_21 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(x_20, x_2, x_3, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(x_1, x_22, x_2, x_3, x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_25 = l_Lean_Name_getPrefix(x_1);
x_26 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(x_25, x_2, x_3, x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(x_1, x_27, x_2, x_3, x_28);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_8);
x_30 = l_Lean_Name_getPrefix(x_1);
x_31 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(x_30, x_2, x_3, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(x_1, x_32, x_2, x_3, x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declRange");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinDeclarationRanges");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DeclarationRanges");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__7;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DeclarationRange");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__12;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__13;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Position");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__16;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__17;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 1;
x_11 = l_Lean_Parser_runParserAttributeHooks(x_2, x_1, x_10, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2;
x_15 = l_Lean_Name_append(x_1, x_14);
lean_inc(x_1);
x_16 = l_Lean_Name_toExprAux(x_1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Lean_mkNatLit(x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_mkNatLit(x_21);
x_23 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19;
x_24 = lean_array_push(x_23, x_20);
x_25 = lean_array_push(x_24, x_22);
x_26 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__18;
x_27 = l_Lean_mkAppN(x_26, x_25);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = lean_ctor_get(x_17, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_mkNatLit(x_31);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lean_mkNatLit(x_33);
x_35 = lean_array_push(x_23, x_32);
x_36 = lean_array_push(x_35, x_34);
x_37 = l_Lean_mkAppN(x_26, x_36);
x_38 = lean_ctor_get(x_17, 3);
lean_inc(x_38);
lean_dec(x_17);
x_39 = l_Lean_mkNatLit(x_38);
x_40 = l_Lean_Parser_declareBuiltinParser___closed__1;
x_41 = lean_array_push(x_40, x_27);
x_42 = lean_array_push(x_41, x_29);
x_43 = lean_array_push(x_42, x_37);
x_44 = lean_array_push(x_43, x_39);
x_45 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__14;
x_46 = l_Lean_mkAppN(x_45, x_44);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_mkNatLit(x_51);
x_53 = lean_array_push(x_23, x_50);
x_54 = lean_array_push(x_53, x_52);
x_55 = l_Lean_mkAppN(x_26, x_54);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
x_57 = l_Lean_mkNatLit(x_56);
x_58 = lean_ctor_get(x_47, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_Lean_mkNatLit(x_61);
x_63 = lean_array_push(x_23, x_60);
x_64 = lean_array_push(x_63, x_62);
x_65 = l_Lean_mkAppN(x_26, x_64);
x_66 = lean_ctor_get(x_47, 3);
lean_inc(x_66);
lean_dec(x_47);
x_67 = l_Lean_mkNatLit(x_66);
x_68 = lean_array_push(x_40, x_55);
x_69 = lean_array_push(x_68, x_57);
x_70 = lean_array_push(x_69, x_65);
x_71 = lean_array_push(x_70, x_67);
x_72 = l_Lean_mkAppN(x_45, x_71);
x_73 = lean_array_push(x_23, x_46);
x_74 = lean_array_push(x_73, x_72);
x_75 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__10;
x_76 = l_Lean_mkAppN(x_75, x_74);
x_77 = lean_array_push(x_23, x_16);
x_78 = lean_array_push(x_77, x_76);
x_79 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__5;
x_80 = l_Lean_mkAppN(x_79, x_78);
lean_inc(x_5);
lean_inc(x_4);
x_81 = l_Lean_declareBuiltin(x_15, x_80, x_4, x_5, x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = 1;
x_84 = l_Lean_Parser_runParserAttributeHooks(x_2, x_1, x_83, x_4, x_5, x_82);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("docString");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinDocString");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_5, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_findDocString_x3f(x_10, x_1, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(x_1, x_2, x_16, x_4, x_5, x_15);
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
x_20 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__2;
x_21 = l_Lean_Name_append(x_1, x_20);
lean_inc(x_1);
x_22 = l_Lean_Name_toExprAux(x_1);
x_23 = l_Lean_mkStrLit(x_19);
x_24 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19;
x_25 = lean_array_push(x_24, x_22);
x_26 = lean_array_push(x_25, x_23);
x_27 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__5;
x_28 = l_Lean_mkAppN(x_27, x_26);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_declareBuiltin(x_21, x_28, x_4, x_5, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(x_1, x_2, x_30, x_4, x_5, x_31);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`Parser` or `TrailingParser` expected)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__4;
x_22 = lean_string_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_27, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__7;
x_34 = lean_string_dec_eq(x_19, x_33);
lean_dec(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_39, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__8;
x_46 = lean_string_dec_eq(x_18, x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = lean_string_dec_eq(x_18, x_33);
lean_dec(x_18);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_52, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_58 = l_Lean_Parser_declareLeadingBuiltinParser(x_2, x_1, x_3, x_5, x_6, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3(x_1, x_2, x_59, x_5, x_6, x_60);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_66 = l_Lean_Parser_declareTrailingBuiltinParser(x_2, x_1, x_3, x_5, x_6, x_12);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3(x_1, x_2, x_67, x_5, x_6, x_68);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_74, 0, x_1);
x_75 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_78, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_84, 0, x_1);
x_85 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_88, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_94, 0, x_1);
x_95 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_98, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_104, 0, x_1);
x_105 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_108, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_114, 0, x_1);
x_115 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_118, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
return x_119;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_119);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_8);
if (x_124 == 0)
{
return x_8;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_8, 0);
x_126 = lean_ctor_get(x_8, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_8);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', must be global");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_Attribute_Builtin_getPrio(x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_128_(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__3(x_18, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4(x_3, x_2, x_10, x_24, x_6, x_7, x_11);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isRec___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
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
x_10 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed), 8, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_registerBuiltinAttribute(x_12, x_6);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Parser_registerBuiltinParserAttribute(x_1, x_2, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser '");
return x_1;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Parser_addToken(x_9, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_3 = x_10;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__3(x_24, x_4, x_5, x_15);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_11, 0);
lean_dec(x_31);
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 4);
lean_dec(x_16);
x_17 = l_Lean_Parser_addSyntaxNodeKind(x_15, x_10);
x_18 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
lean_ctor_set(x_12, 4, x_18);
lean_ctor_set(x_12, 0, x_17);
x_19 = lean_st_ref_set(x_6, x_12, x_13);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_box(0);
x_2 = x_22;
x_4 = x_23;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
x_28 = lean_ctor_get(x_12, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_29 = l_Lean_Parser_addSyntaxNodeKind(x_25, x_10);
x_30 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_st_ref_set(x_6, x_31, x_13);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
x_35 = lean_usize_add(x_2, x_34);
x_36 = lean_box(0);
x_2 = x_35;
x_4 = x_36;
x_7 = x_33;
goto _start;
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(x_38, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
x_43 = lean_usize_add(x_2, x_42);
x_2 = x_43;
x_4 = x_40;
x_7 = x_41;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
default: 
{
size_t x_49; size_t x_50; 
x_49 = 1;
x_50 = lean_usize_add(x_2, x_49);
x_2 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_fget(x_2, x_5);
x_14 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
x_15 = lean_apply_6(x_1, x_6, x_13, x_14, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_16;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg___boxed), 9, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = l_Lean_Parser_addSyntaxNodeKind(x_11, x_2);
x_14 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
lean_ctor_set(x_8, 4, x_14);
lean_ctor_set(x_8, 0, x_13);
x_15 = lean_st_ref_set(x_5, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
x_24 = lean_ctor_get(x_8, 2);
x_25 = lean_ctor_get(x_8, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_26 = l_Lean_Parser_addSyntaxNodeKind(x_22, x_2);
x_27 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1;
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_st_ref_set(x_5, x_28, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(x_6, x_13, x_14, x_2, x_3, x_4, x_5);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___closed__1;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg(x_18, x_16, x_17, lean_box(0), x_19, x_2, x_3, x_4, x_5);
lean_dec(x_17);
lean_dec(x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Attribute_Builtin_getPrio(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_16 = l_Lean_Parser_isParserCategory___closed__1;
x_17 = l_Lean_ScopedEnvExtension_getState___rarg(x_15, x_16, x_14);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_6, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_2);
lean_inc(x_18);
x_26 = l_Lean_Parser_mkParserOfConstant(x_18, x_2, x_24, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_box(0);
x_34 = lean_apply_1(x_32, x_33);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_35 = l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(x_2, x_4, x_34, x_5, x_6, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3;
x_39 = lean_apply_1(x_37, x_38);
x_40 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__3(x_39, x_40, x_5, x_6, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_30);
lean_inc(x_2);
lean_inc(x_1);
x_43 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_30);
lean_ctor_set(x_43, 3, x_9);
x_44 = lean_unbox(x_29);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_44);
x_45 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_1);
x_46 = l_Lean_Parser_addParser(x_18, x_1, x_2, x_45, x_30, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_49, x_5, x_6, x_42);
lean_dec(x_6);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
lean_dec(x_46);
lean_inc(x_5);
x_55 = l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3(x_16, x_43, x_4, x_5, x_6, x_42);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = 0;
x_58 = l_Lean_Parser_runParserAttributeHooks(x_1, x_2, x_57, x_5, x_6, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_41, 0);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_41);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_35);
if (x_63 == 0)
{
return x_35;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_35, 0);
x_65 = lean_ctor_get(x_35, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_35);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_26, 0);
x_69 = lean_io_error_to_string(x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_25);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_26, 0, x_72);
return x_26;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_26, 0);
x_74 = lean_ctor_get(x_26, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_26);
x_75 = lean_io_error_to_string(x_73);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_25);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_8);
if (x_80 == 0)
{
return x_8;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_8, 0);
x_82 = lean_ctor_get(x_8, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_8);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__5(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2;
x_5 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg___boxed), 7, 0);
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
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Parser_mkParserAttributeImpl___closed__1;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg___boxed), 7, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Parser_mkParserAttributeImpl___closed__2;
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_mkParserAttributeImpl___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserAttributeImpl___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_mkParserAttributeImpl___elambda__2___rarg(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserAttributeImpl___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_mkParserAttributeImpl(x_1, x_2);
x_5 = l_Lean_registerBuiltinAttribute(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid parser attribute implementation builder arguments");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2;
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
x_5 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2;
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
x_12 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2;
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2;
return x_13;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2;
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parserAttr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__3;
x_4 = l_Lean_registerAttributeImplBuilder(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_6 = l_Lean_Parser_addParserCategory(x_1, x_3, x_4);
x_7 = l_IO_ofExcept___at_Lean_declareBuiltin___spec__2(x_6, x_5);
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
x_15 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_registerParserCategory(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTermParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCommandParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__2;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4;
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 6);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 2);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_17);
x_21 = l_Lean_ResolveName_resolveNamespace_x3f(x_17, x_19, x_20, x_7);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
if (lean_obj_tag(x_21) == 0)
{
lean_free_object(x_8);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_3 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_5, 6);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lean_Parser_isParserCategory___closed__1;
lean_inc(x_33);
x_35 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_34, x_17, x_33);
if (x_1 == 0)
{
lean_dec(x_33);
lean_ctor_set(x_8, 0, x_35);
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set(x_8, 3, x_39);
lean_ctor_set(x_8, 0, x_35);
x_3 = x_23;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = l_Lean_Parser_isParserCategory___closed__1;
lean_inc(x_41);
x_43 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_42, x_17, x_41);
if (x_1 == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_ctor_set(x_8, 0, x_43);
x_44 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_8);
lean_ctor_set(x_44, 2, x_10);
lean_ctor_set(x_44, 3, x_11);
lean_ctor_set(x_44, 4, x_12);
lean_ctor_set(x_44, 5, x_14);
lean_ctor_set(x_44, 6, x_15);
lean_ctor_set_uint8(x_44, sizeof(void*)*7, x_13);
x_3 = x_23;
x_5 = x_44;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_20);
lean_ctor_set(x_8, 3, x_48);
lean_ctor_set(x_8, 0, x_43);
x_49 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_8);
lean_ctor_set(x_49, 2, x_10);
lean_ctor_set(x_49, 3, x_11);
lean_ctor_set(x_49, 4, x_12);
lean_ctor_set(x_49, 5, x_14);
lean_ctor_set(x_49, 6, x_15);
lean_ctor_set_uint8(x_49, sizeof(void*)*7, x_13);
x_3 = x_23;
x_5 = x_49;
goto _start;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get(x_8, 1);
x_53 = lean_ctor_get(x_8, 2);
x_54 = lean_ctor_get(x_8, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_8);
lean_inc(x_51);
x_55 = l_Lean_ResolveName_resolveNamespace_x3f(x_51, x_53, x_54, x_7);
x_56 = 1;
x_57 = lean_usize_add(x_3, x_56);
if (lean_obj_tag(x_55) == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_3 = x_57;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_59 = x_5;
} else {
 lean_dec_ref(x_5);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = l_Lean_Parser_isParserCategory___closed__1;
lean_inc(x_60);
x_62 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_61, x_51, x_60);
if (x_1 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 7, 1);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_9);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_10);
lean_ctor_set(x_64, 3, x_11);
lean_ctor_set(x_64, 4, x_12);
lean_ctor_set(x_64, 5, x_14);
lean_ctor_set(x_64, 6, x_15);
lean_ctor_set_uint8(x_64, sizeof(void*)*7, x_13);
x_3 = x_57;
x_5 = x_64;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_54);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_52);
lean_ctor_set(x_69, 2, x_53);
lean_ctor_set(x_69, 3, x_68);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 7, 1);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_10);
lean_ctor_set(x_70, 3, x_11);
lean_ctor_set(x_70, 4, x_12);
lean_ctor_set(x_70, 5, x_14);
lean_ctor_set(x_70, 6, x_15);
lean_ctor_set_uint8(x_70, sizeof(void*)*7, x_13);
x_3 = x_57;
x_5 = x_70;
goto _start;
}
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_array_get_size(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
x_6 = x_4;
goto block_30;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
x_6 = x_4;
goto block_30;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_37 = l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___spec__1(x_3, x_1, x_35, x_36, x_4);
x_6 = x_37;
goto block_30;
}
}
block_30:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_12 = l_Lean_Parser_isParserCategory___closed__1;
x_13 = l_Lean_ScopedEnvExtension_getState___rarg(x_11, x_12, x_10);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_6, 3, x_14);
x_15 = lean_apply_2(x_2, x_6, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
x_24 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_25 = l_Lean_Parser_isParserCategory___closed__1;
x_26 = l_Lean_ScopedEnvExtension_getState___rarg(x_24, x_25, x_23);
lean_dec(x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_19);
lean_ctor_set(x_28, 5, x_21);
lean_ctor_set(x_28, 6, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*7, x_20);
x_29 = lean_apply_2(x_2, x_28, x_5);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___spec__1(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Parser_withOpenDeclFnCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withOpenDeclFnCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
x_2 = l_Lean_Parser_withOpenDeclFnCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_withOpenDeclFnCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openSimple");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withOpenDeclFnCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_withOpenDeclFnCore___closed__2;
x_2 = l_Lean_Parser_withOpenDeclFnCore___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_withOpenDeclFnCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openScoped");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withOpenDeclFnCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_withOpenDeclFnCore___closed__2;
x_2 = l_Lean_Parser_withOpenDeclFnCore___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Parser_withOpenDeclFnCore___closed__4;
x_7 = lean_name_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Parser_withOpenDeclFnCore___closed__6;
x_9 = lean_name_eq(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1(x_15, x_16, x_13);
x_18 = 0;
x_19 = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(x_17, x_2, x_18, x_3, x_4);
lean_dec(x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1(x_24, x_25, x_22);
x_27 = 1;
x_28 = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(x_26, x_2, x_27, x_3, x_4);
lean_dec(x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Parser_withOpenDeclFnCore___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_withOpenFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("open");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withOpenFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_withOpenDeclFnCore___closed__2;
x_2 = l_Lean_Parser_withOpenFn___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_apply_2(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_instInhabitedSyntax;
x_10 = l_Array_back___rarg(x_9, x_4);
lean_dec(x_4);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l_Lean_Parser_withOpenFn___closed__2;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_10, x_15);
lean_dec(x_10);
x_17 = l_Lean_Parser_withOpenDeclFnCore(x_16, x_1, x_2, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_apply_2(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_instInhabitedSyntax;
x_10 = l_Array_back___rarg(x_9, x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_withOpenDeclFnCore(x_10, x_1, x_2, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to determine parser using syntax stack, the specified element on the stack is not an identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown parser ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected parser to return exactly one syntax object");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous parser name ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to determine parser using syntax stack, stack is too small");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_nat_sub(x_5, x_1);
x_10 = lean_nat_sub(x_9, x_6);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_array_get(x_11, x_4, x_10);
lean_dec(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_2);
x_14 = l_Lean_Parser_ParserContext_resolveName(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = 1;
x_16 = l_Lean_Name_toString(x_13, x_15);
x_17 = l_Lean_Parser_parserOfStackFn___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Parser_evalParserConstUnsafe(x_26, x_2, x_3);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = lean_box(0);
x_30 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_810____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_dec(x_5);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
x_33 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_box(0);
x_36 = l_Lean_Parser_parserOfStackFn___closed__3;
x_37 = l_Lean_Parser_ParserState_mkUnexpectedError(x_27, x_36, x_35);
return x_37;
}
else
{
return x_27;
}
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_2);
x_38 = 1;
x_39 = l_Lean_Name_toString(x_13, x_38);
x_40 = l_Lean_Parser_parserOfStackFn___closed__4;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_43, x_44);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_2);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_dec(x_14);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = 1;
x_48 = l_Lean_Name_toString(x_13, x_47);
x_49 = l_Lean_Parser_parserOfStackFn___closed__2;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_52, x_53);
return x_54;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_46);
x_55 = 1;
x_56 = l_Lean_Name_toString(x_13, x_55);
x_57 = l_Lean_Parser_parserOfStackFn___closed__4;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_box(0);
x_62 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_60, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = l_Lean_Parser_parserOfStackFn___closed__1;
x_65 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_64, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = l_Lean_Parser_parserOfStackFn___closed__5;
x_68 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_67, x_66);
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_parserOfStackFn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
lean_ctor_set(x_3, 2, x_2);
x_7 = l_Lean_Parser_parserOfStackFn(x_1, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set(x_15, 6, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_12);
x_16 = l_Lean_Parser_parserOfStackFn(x_1, x_15, x_4);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Parser_parserOfStack___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___elambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_parserOfStack___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_parserOfStack___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_StrInterpolation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6____closed__1);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
lean_dec_ref(res);
}l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35____closed__3);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_35_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinSyntaxNodeKindSetRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinSyntaxNodeKindSetRef);
lean_dec_ref(res);
}l_Lean_Parser_registerBuiltinNodeKind___closed__1 = _init_l_Lean_Parser_registerBuiltinNodeKind___closed__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinNodeKind___closed__1);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_74_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_180_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinParserCategoriesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinParserCategoriesRef);
lean_dec_ref(res);
}l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___rarg___closed__2);
l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__1 = _init_l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__1();
l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2 = _init_l_Std_PersistentHashMap_containsAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore___spec__5___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__2);
l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1 = _init_l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__1);
l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__2 = _init_l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__2();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry___closed__2);
l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry = _init_l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry);
l_Lean_Parser_ParserExtension_instInhabitedEntry___closed__1 = _init_l_Lean_Parser_ParserExtension_instInhabitedEntry___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedEntry___closed__1);
l_Lean_Parser_ParserExtension_instInhabitedEntry = _init_l_Lean_Parser_ParserExtension_instInhabitedEntry();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedEntry);
l_Lean_Parser_ParserExtension_State_tokens___default = _init_l_Lean_Parser_ParserExtension_State_tokens___default();
lean_mark_persistent(l_Lean_Parser_ParserExtension_State_tokens___default);
l_Lean_Parser_ParserExtension_State_kinds___default = _init_l_Lean_Parser_ParserExtension_State_kinds___default();
lean_mark_persistent(l_Lean_Parser_ParserExtension_State_kinds___default);
l_Lean_Parser_ParserExtension_State_categories___default = _init_l_Lean_Parser_ParserExtension_State_categories___default();
lean_mark_persistent(l_Lean_Parser_ParserExtension_State_categories___default);
l_Lean_Parser_ParserExtension_instInhabitedState___closed__1 = _init_l_Lean_Parser_ParserExtension_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState___closed__1);
l_Lean_Parser_ParserExtension_instInhabitedState___closed__2 = _init_l_Lean_Parser_ParserExtension_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState___closed__2);
l_Lean_Parser_ParserExtension_instInhabitedState = _init_l_Lean_Parser_ParserExtension_instInhabitedState();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState);
l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__2);
l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1 = _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_throwUnknownParserCategory___rarg___closed__1);
l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2 = _init_l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_throwUnknownParserCategory___rarg___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__2);
l_Lean_Parser_ParserExtension_addEntryImpl___closed__1 = _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1);
l_Lean_Parser_ParserExtension_addEntryImpl___closed__2 = _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__2();
lean_mark_persistent(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2);
l_Lean_Parser_ParserExtension_addEntryImpl___closed__3 = _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__3();
lean_mark_persistent(l_Lean_Parser_ParserExtension_addEntryImpl___closed__3);
l_Lean_Parser_ParserExtension_addEntryImpl___closed__4 = _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__4();
lean_mark_persistent(l_Lean_Parser_ParserExtension_addEntryImpl___closed__4);
l_Lean_Parser_ParserExtension_addEntryImpl___closed__5 = _init_l_Lean_Parser_ParserExtension_addEntryImpl___closed__5();
lean_mark_persistent(l_Lean_Parser_ParserExtension_addEntryImpl___closed__5);
l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1 = _init_l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__1);
l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2 = _init_l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_registerAliasCore___rarg___lambda__2___closed__2);
l_Lean_Parser_registerAliasCore___rarg___closed__1 = _init_l_Lean_Parser_registerAliasCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_registerAliasCore___rarg___closed__1);
l_Lean_Parser_registerAliasCore___rarg___closed__2 = _init_l_Lean_Parser_registerAliasCore___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_registerAliasCore___rarg___closed__2);
l_Lean_Parser_getConstAlias___rarg___closed__1 = _init_l_Lean_Parser_getConstAlias___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_getConstAlias___rarg___closed__1);
l_Lean_Parser_getConstAlias___rarg___closed__2 = _init_l_Lean_Parser_getConstAlias___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_getConstAlias___rarg___closed__2);
l_Lean_Parser_getConstAlias___rarg___closed__3 = _init_l_Lean_Parser_getConstAlias___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_getConstAlias___rarg___closed__3);
l_Lean_Parser_getConstAlias___rarg___closed__4 = _init_l_Lean_Parser_getConstAlias___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_getConstAlias___rarg___closed__4);
l_Lean_Parser_getUnaryAlias___rarg___closed__1 = _init_l_Lean_Parser_getUnaryAlias___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_getUnaryAlias___rarg___closed__1);
l_Lean_Parser_getBinaryAlias___rarg___closed__1 = _init_l_Lean_Parser_getBinaryAlias___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_getBinaryAlias___rarg___closed__1);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1932_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliasesRef);
lean_dec_ref(res);
}l_Lean_Parser_registerAlias___closed__1 = _init_l_Lean_Parser_registerAlias___closed__1();
lean_mark_persistent(l_Lean_Parser_registerAlias___closed__1);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__1 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__2 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__2();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__3 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__3();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__4 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__4();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__5 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__5();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__6 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__6();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__7 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__7();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7);
l_Lean_Parser_mkParserOfConstantUnsafe___closed__8 = _init_l_Lean_Parser_mkParserOfConstantUnsafe___closed__8();
lean_mark_persistent(l_Lean_Parser_mkParserOfConstantUnsafe___closed__8);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3058_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAttributeHooks = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAttributeHooks);
lean_dec_ref(res);
}l_Lean_Parser_registerParserAttributeHook___closed__1 = _init_l_Lean_Parser_registerParserAttributeHook___closed__1();
lean_mark_persistent(l_Lean_Parser_registerParserAttributeHook___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____lambda__2___closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__6);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__7 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__7();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139____closed__7);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3139_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181____closed__6);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3181_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__6);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__7);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__8 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__8();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335____closed__8);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3335_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserExtension);
lean_dec_ref(res);
}l_Lean_Parser_isParserCategory___closed__1 = _init_l_Lean_Parser_isParserCategory___closed__1();
lean_mark_persistent(l_Lean_Parser_isParserCategory___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517____closed__6);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3517_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_internal_parseQuotWithCurrentStage = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_internal_parseQuotWithCurrentStage);
lean_dec_ref(res);
}l_Lean_Parser_evalInsideQuot___elambda__1___closed__1 = _init_l_Lean_Parser_evalInsideQuot___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_evalInsideQuot___elambda__1___closed__1);
l_Lean_Parser_categoryParserFnImpl___closed__1 = _init_l_Lean_Parser_categoryParserFnImpl___closed__1();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__1);
l_Lean_Parser_categoryParserFnImpl___closed__2 = _init_l_Lean_Parser_categoryParserFnImpl___closed__2();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__2);
l_Lean_Parser_categoryParserFnImpl___closed__3 = _init_l_Lean_Parser_categoryParserFnImpl___closed__3();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__3);
l_Lean_Parser_categoryParserFnImpl___closed__4 = _init_l_Lean_Parser_categoryParserFnImpl___closed__4();
lean_mark_persistent(l_Lean_Parser_categoryParserFnImpl___closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785____closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3785_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Parser_addToken___spec__3___closed__1);
l_Lean_Parser_isValidSyntaxNodeKind___closed__1 = _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__1();
l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Lean_Parser_getSyntaxNodeKinds___spec__2___closed__1);
l_Lean_Parser_mkParserState___closed__1 = _init_l_Lean_Parser_mkParserState___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserState___closed__1);
l_Lean_Parser_runParserCategory___closed__1 = _init_l_Lean_Parser_runParserCategory___closed__1();
lean_mark_persistent(l_Lean_Parser_runParserCategory___closed__1);
l_Lean_Parser_declareBuiltinParser___closed__1 = _init_l_Lean_Parser_declareBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__1);
l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__1);
l_Lean_Parser_declareLeadingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__2);
l_Lean_Parser_declareLeadingBuiltinParser___closed__3 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__3();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__3);
l_Lean_Parser_declareLeadingBuiltinParser___closed__4 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__4();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__4);
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
l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1 = _init_l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRangesCore_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__3___closed__1);
l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___closed__1 = _init_l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___lambda__1___closed__1);
l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___closed__1 = _init_l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRanges_x3f___at___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___spec__1___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__3);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__4 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__4);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__5 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__5);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__6 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__6);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__7 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__7);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__8);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__9 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__9);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__10 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__10);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__11 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__11);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__12 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__12();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__12);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__13 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__13();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__13);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__14 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__14();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__14);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__15 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__15();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__15);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__16 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__16();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__16);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__17 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__17();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__17);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__18 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__18();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__18);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__2___closed__19);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__3);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__4 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__4);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__5 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__3___closed__5);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___lambda__4___closed__3);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__4 = _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__4();
lean_mark_persistent(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__4);
l_Lean_Parser_registerBuiltinParserAttribute___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1 = _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1();
lean_mark_persistent(l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__1);
l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2 = _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2();
lean_mark_persistent(l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__2);
l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3 = _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3();
lean_mark_persistent(l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__3);
l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4 = _init_l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4();
lean_mark_persistent(l_List_forM___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__1___closed__4);
l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___spec__4___closed__1);
l_Lean_Parser_mkParserAttributeImpl___closed__1 = _init_l_Lean_Parser_mkParserAttributeImpl___closed__1();
lean_mark_persistent(l_Lean_Parser_mkParserAttributeImpl___closed__1);
l_Lean_Parser_mkParserAttributeImpl___closed__2 = _init_l_Lean_Parser_mkParserAttributeImpl___closed__2();
lean_mark_persistent(l_Lean_Parser_mkParserAttributeImpl___closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____lambda__1___closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085____closed__3);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5085_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191____closed__4);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5191_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202____closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5202_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213____closed__4);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5213_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224____closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_5224_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_withOpenDeclFnCore___closed__1 = _init_l_Lean_Parser_withOpenDeclFnCore___closed__1();
lean_mark_persistent(l_Lean_Parser_withOpenDeclFnCore___closed__1);
l_Lean_Parser_withOpenDeclFnCore___closed__2 = _init_l_Lean_Parser_withOpenDeclFnCore___closed__2();
lean_mark_persistent(l_Lean_Parser_withOpenDeclFnCore___closed__2);
l_Lean_Parser_withOpenDeclFnCore___closed__3 = _init_l_Lean_Parser_withOpenDeclFnCore___closed__3();
lean_mark_persistent(l_Lean_Parser_withOpenDeclFnCore___closed__3);
l_Lean_Parser_withOpenDeclFnCore___closed__4 = _init_l_Lean_Parser_withOpenDeclFnCore___closed__4();
lean_mark_persistent(l_Lean_Parser_withOpenDeclFnCore___closed__4);
l_Lean_Parser_withOpenDeclFnCore___closed__5 = _init_l_Lean_Parser_withOpenDeclFnCore___closed__5();
lean_mark_persistent(l_Lean_Parser_withOpenDeclFnCore___closed__5);
l_Lean_Parser_withOpenDeclFnCore___closed__6 = _init_l_Lean_Parser_withOpenDeclFnCore___closed__6();
lean_mark_persistent(l_Lean_Parser_withOpenDeclFnCore___closed__6);
l_Lean_Parser_withOpenFn___closed__1 = _init_l_Lean_Parser_withOpenFn___closed__1();
lean_mark_persistent(l_Lean_Parser_withOpenFn___closed__1);
l_Lean_Parser_withOpenFn___closed__2 = _init_l_Lean_Parser_withOpenFn___closed__2();
lean_mark_persistent(l_Lean_Parser_withOpenFn___closed__2);
l_Lean_Parser_parserOfStackFn___closed__1 = _init_l_Lean_Parser_parserOfStackFn___closed__1();
lean_mark_persistent(l_Lean_Parser_parserOfStackFn___closed__1);
l_Lean_Parser_parserOfStackFn___closed__2 = _init_l_Lean_Parser_parserOfStackFn___closed__2();
lean_mark_persistent(l_Lean_Parser_parserOfStackFn___closed__2);
l_Lean_Parser_parserOfStackFn___closed__3 = _init_l_Lean_Parser_parserOfStackFn___closed__3();
lean_mark_persistent(l_Lean_Parser_parserOfStackFn___closed__3);
l_Lean_Parser_parserOfStackFn___closed__4 = _init_l_Lean_Parser_parserOfStackFn___closed__4();
lean_mark_persistent(l_Lean_Parser_parserOfStackFn___closed__4);
l_Lean_Parser_parserOfStackFn___closed__5 = _init_l_Lean_Parser_parserOfStackFn___closed__5();
lean_mark_persistent(l_Lean_Parser_parserOfStackFn___closed__5);
l_Lean_Parser_parserOfStack___closed__1 = _init_l_Lean_Parser_parserOfStack___closed__1();
lean_mark_persistent(l_Lean_Parser_parserOfStack___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
