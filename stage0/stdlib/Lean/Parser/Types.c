// Lean compiler output
// Module: Lean.Parser.Types
// Imports: Init Lean.Data.Trie Lean.Syntax Lean.Message
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
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withCacheFn___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo;
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedError___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenCacheEntry_token___default;
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Parser_withCacheFn___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenCacheEntry_startPos___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_empty;
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__1;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey;
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserModuleContext_currNamespace___default;
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235_(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Parser_info___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_instToStringError;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__1;
static lean_object* l_Lean_Parser_instBEqParserCacheKey___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Parser_withCacheFn___spec__12(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3;
static lean_object* l_Lean_Parser_Parser_info___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_errorMsg___default;
static lean_object* l_Lean_Parser_SyntaxStack_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Parser_withCacheFn___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Parser_withCacheFn___spec__5___at_Lean_Parser_withCacheFn___spec__6(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps_loop___at_Lean_Parser_Error_toString___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Parser_withCacheFn___spec__12___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instBEqCacheableParserContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_withCacheFn___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext;
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stxStack___default;
static lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Parser_withCacheFn___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2;
static lean_object* l_Lean_Parser_Error_toString___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__3;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_unexpectedTk___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Parser_initCacheForInput___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Parser_initCacheForInput___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_CacheableParserContext_forbiddenTk_x3f___default;
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Parser_withCacheFn___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_CacheableParserContext_quotDepth___default;
LEAN_EXPORT lean_object* l_Lean_Parser_CacheableParserContext_savedPos_x3f___default;
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Parser_withCacheFn___spec__10___closed__1;
static lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initCacheForInput___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default;
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lean_Parser_Error_instToStringError___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedInputContext;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Parser_withCacheFn___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedError;
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__4;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_unexpected___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default___boxed(lean_object*);
lean_object* l_String_csize(uint32_t);
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser;
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(lean_object*);
static lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPos;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__2;
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3;
static lean_object* l_Lean_Parser_withCacheFn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withCacheFn___lambda__2___closed__3;
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_argPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_instToStringFirstTokens;
uint8_t l_List_beq___at___private_Init_Meta_0__Lean_Syntax_beqPreresolved____x40_Init_Meta___hyg_3119____spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_firstTokens___default;
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenCacheEntry_stopPos___default;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__2(lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pos___default;
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Parser_withCacheFn___spec__11(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withResetCacheFn___lambda__1___closed__1;
static lean_object* l_Lean_Parser_Parser_info___default___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError;
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps___at_Lean_Parser_Error_toString___spec__2(lean_object*);
static lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_withCacheFn___spec__8(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserFn_run___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendSyntaxStackArraySyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed(lean_object*);
extern lean_object* l_Id_instMonadId;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_expected___default;
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_withCacheFn___spec__9(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_lhsPrec___default;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg___boxed(lean_object*);
static lean_object* l_Lean_Parser_instBEqError___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_minPrec;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_FirstTokens_toStr___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserModuleContext_openDecls___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_leadPrec;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedFirstTokens;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_CacheableParserContext_suppressInsideQuot___default;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; 
x_3 = lean_string_utf8_next(x_1, x_2);
x_4 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_getNext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_maxPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1024u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_argPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1023u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_leadPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1022u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_minPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(10u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Name_hash___override(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__2;
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
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__2;
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
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_5, x_8, x_9, x_2, x_3);
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
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_13, x_16, x_17, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserModuleContext_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserModuleContext_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_CacheableParserContext_quotDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static uint8_t _init_l_Lean_Parser_CacheableParserContext_suppressInsideQuot___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_CacheableParserContext_savedPos_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_CacheableParserContext_forbiddenTk_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__2(lean_object* x_1, lean_object* x_2) {
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
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_18 = lean_nat_dec_eq(x_3, x_8);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_4, x_9);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
if (x_5 == 0)
{
if (x_10 == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_13 = x_22;
goto block_17;
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
if (x_10 == 0)
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_box(0);
x_13 = x_25;
goto block_17;
}
}
}
}
block_17:
{
uint8_t x_14; 
lean_dec(x_13);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1(x_6, x_11);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__2(x_7, x_12);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqCacheableParserContext___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_unexpectedTk___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_unexpected___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_expected___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedError___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Syntax_structEq(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_List_beq___at___private_Init_Meta_0__Lean_Syntax_beqPreresolved____x40_Init_Meta___hyg_3119____spec__1(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqError___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" or ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__2;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
}
}
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps_loop___at_Lean_Parser_Error_toString___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_string_dec_eq(x_1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_1);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_7);
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_string_dec_eq(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
x_1 = x_12;
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at_Lean_Parser_Error_toString___spec__2(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_List_eraseReps_loop___at_Lean_Parser_Error_toString___spec__3(x_3, x_4, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("; ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_appendTR___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Error_toString___closed__2;
x_2 = l_Lean_Parser_Error_toString___closed__3;
x_3 = l_String_intercalate(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_4 = lean_string_dec_eq(x_2, x_3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_List_beq___at___private_Init_Meta_0__Lean_Syntax_beqPreresolved____x40_Init_Meta___hyg_3119____spec__1(x_5, x_6);
if (x_4 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = l_List_redLength___rarg(x_5);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_5, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_11, x_15, x_14);
lean_dec(x_14);
x_17 = lean_array_to_list(lean_box(0), x_16);
x_18 = l_List_eraseReps___at_Lean_Parser_Error_toString___spec__2(x_17);
x_19 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(x_18);
x_20 = l_Lean_Parser_Error_toString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = l_List_appendTR___rarg(x_8, x_22);
x_24 = l_Lean_Parser_Error_toString___closed__2;
x_25 = l_String_intercalate(x_24, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_26 = l_List_appendTR___rarg(x_8, x_6);
x_27 = l_Lean_Parser_Error_toString___closed__2;
x_28 = l_String_intercalate(x_27, x_26);
return x_28;
}
}
else
{
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = l_List_redLength___rarg(x_5);
x_30 = lean_mk_empty_array_with_capacity(x_29);
lean_dec(x_29);
x_31 = l_List_toArrayAux___rarg(x_5, x_30);
x_32 = lean_array_get_size(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_32, x_33);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_31, x_35, x_34);
lean_dec(x_34);
x_37 = lean_array_to_list(lean_box(0), x_36);
x_38 = l_List_eraseReps___at_Lean_Parser_Error_toString___spec__2(x_37);
x_39 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(x_38);
x_40 = l_Lean_Parser_Error_toString___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
x_43 = l_List_appendTR___rarg(x_6, x_42);
x_44 = l_Lean_Parser_Error_toString___closed__2;
x_45 = l_String_intercalate(x_44, x_43);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_5);
x_46 = l_Lean_Parser_Error_toString___closed__4;
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Error_instToStringError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Error_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_instToStringError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_instToStringError___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_7 = lean_string_dec_eq(x_4, x_6);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_List_appendTR___rarg(x_10, x_5);
if (x_7 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_List_appendTR___rarg(x_14, x_5);
if (x_7 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Parser_TokenCacheEntry_startPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_TokenCacheEntry_stopPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_TokenCacheEntry_token___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = l___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_235_(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_name_eq(x_4, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_5, x_8);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqParserCacheKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqParserCacheKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqParserCacheKey___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_uint64_of_nat(x_2);
x_5 = l_Lean_Name_hash___override(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_instHashableParserCacheKey(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Parser_initCacheForInput___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_String_csize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_Lean_Parser_initCacheForInput___closed__1;
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(8u);
x_9 = l_Lean_mkHashMapImp___rarg(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Parser_initCacheForInput___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Parser_initCacheForInput___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = l_Array_toSubarray___rarg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_SyntaxStack_empty___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_SyntaxStack_size(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_SyntaxStack_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_SyntaxStack_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = l_Array_shrink___rarg(x_4, x_6);
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_7);
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
x_10 = lean_nat_add(x_9, x_2);
x_11 = l_Array_shrink___rarg(x_8, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_SyntaxStack_shrink(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_array_push(x_6, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_SyntaxStack_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
lean_dec(x_2);
if (x_4 == 0)
{
return x_1;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_pop(x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_array_pop(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedSyntax;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Parser.Types", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Parser.SyntaxStack.back", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SyntaxStack.back: element is inaccessible", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_SyntaxStack_back___closed__1;
x_2 = l_Lean_Parser_SyntaxStack_back___closed__2;
x_3 = lean_unsigned_to_nat(174u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Parser_SyntaxStack_back___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_SyntaxStack_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Lean_Parser_SyntaxStack_back___closed__4;
x_6 = l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_instInhabitedSyntax;
x_9 = l_Array_back___rarg(x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Parser.SyntaxStack.get!", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SyntaxStack.get!: element is inaccessible", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_SyntaxStack_back___closed__1;
x_2 = l_Lean_Parser_SyntaxStack_get_x21___closed__1;
x_3 = lean_unsigned_to_nat(180u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Parser_SyntaxStack_get_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Parser_SyntaxStack_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_SyntaxStack_get_x21___closed__3;
x_6 = l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_nat_add(x_8, x_2);
x_10 = l_Lean_instInhabitedSyntax;
x_11 = lean_array_get(x_10, x_7, x_9);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_SyntaxStack_get_x21(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = lean_nat_add(x_5, x_3);
x_8 = l_Array_extract___rarg(x_4, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_SyntaxStack_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendSyntaxStackArraySyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Array_append___rarg(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Array_append___rarg(x_6, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_ParserState_stxStack___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_SyntaxStack_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_lhsPrec___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_errorMsg___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_499_(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserState_hasError(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Parser_SyntaxStack_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserState_stackSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 4);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_dec(x_7);
x_8 = l_Lean_Parser_SyntaxStack_shrink(x_5, x_2);
x_9 = lean_box(0);
lean_ctor_set(x_1, 4, x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Lean_Parser_SyntaxStack_shrink(x_10, x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_restore(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_2);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Parser_SyntaxStack_push(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = l_Lean_Parser_SyntaxStack_push(x_6, x_2);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Parser_SyntaxStack_pop(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = l_Lean_Parser_SyntaxStack_pop(x_5);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Parser_SyntaxStack_shrink(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = l_Lean_Parser_SyntaxStack_shrink(x_6, x_2);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_shrinkStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_string_utf8_next(x_2, x_3);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_string_utf8_next(x_2, x_3);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_dec(x_6);
x_7 = lean_string_utf8_next_fast(x_2, x_3);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_next_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = l_Lean_Parser_instInhabitedInputContext___closed__2;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_FileMap_toPosition(x_6, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_Parser_Error_toString(x_5);
x_11 = lean_box(0);
x_12 = l_Lean_mkErrorStringWithPos(x_9, x_8, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_toErrorMsg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_SyntaxStack_size(x_5);
x_10 = lean_nat_dec_eq(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Parser_SyntaxStack_extract(x_5, x_3, x_9);
lean_dec(x_9);
x_12 = lean_box(2);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_11);
x_14 = l_Lean_Parser_SyntaxStack_shrink(x_5, x_3);
x_15 = l_Lean_Parser_SyntaxStack_push(x_14, x_13);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_SyntaxStack_push(x_5, x_16);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_Parser_SyntaxStack_size(x_5);
x_19 = l_Lean_Parser_SyntaxStack_extract(x_5, x_3, x_18);
lean_dec(x_18);
x_20 = lean_box(2);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_19);
x_22 = l_Lean_Parser_SyntaxStack_shrink(x_5, x_3);
x_23 = l_Lean_Parser_SyntaxStack_push(x_22, x_21);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
x_28 = lean_ctor_get(x_1, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_29 = lean_box(0);
lean_inc(x_28);
x_30 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Parser_SyntaxStack_size(x_24);
x_32 = lean_nat_dec_eq(x_31, x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = l_Lean_Parser_SyntaxStack_extract(x_24, x_3, x_31);
lean_dec(x_31);
x_34 = lean_box(2);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_33);
x_36 = l_Lean_Parser_SyntaxStack_shrink(x_24, x_3);
x_37 = l_Lean_Parser_SyntaxStack_push(x_36, x_35);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
lean_ctor_set(x_38, 3, x_27);
lean_ctor_set(x_38, 4, x_28);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_2);
x_39 = lean_box(0);
x_40 = l_Lean_Parser_SyntaxStack_push(x_24, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_27);
lean_ctor_set(x_41, 4, x_28);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = l_Lean_Parser_SyntaxStack_size(x_24);
x_43 = l_Lean_Parser_SyntaxStack_extract(x_24, x_3, x_42);
lean_dec(x_42);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_43);
x_46 = l_Lean_Parser_SyntaxStack_shrink(x_24, x_3);
x_47 = l_Lean_Parser_SyntaxStack_push(x_46, x_45);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_25);
lean_ctor_set(x_48, 2, x_26);
lean_ctor_set(x_48, 3, x_27);
lean_ctor_set(x_48, 4, x_28);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mkNode(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = l_Lean_Parser_SyntaxStack_size(x_5);
x_9 = l_Lean_Parser_SyntaxStack_extract(x_5, x_7, x_8);
lean_dec(x_8);
x_10 = lean_box(2);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_9);
x_12 = l_Lean_Parser_SyntaxStack_shrink(x_5, x_7);
lean_dec(x_7);
x_13 = l_Lean_Parser_SyntaxStack_push(x_12, x_11);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
x_21 = l_Lean_Parser_SyntaxStack_size(x_14);
x_22 = l_Lean_Parser_SyntaxStack_extract(x_14, x_20, x_21);
lean_dec(x_21);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_22);
x_25 = l_Lean_Parser_SyntaxStack_shrink(x_14, x_20);
lean_dec(x_20);
x_26 = l_Lean_Parser_SyntaxStack_push(x_25, x_24);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set(x_27, 4, x_18);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mkTrailingNode(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_1, 4, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_11, 4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_4);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 4);
lean_dec(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_1, 4, x_10);
x_11 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set(x_17, 4, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_5);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_dec(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_1, 4, x_9);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_5);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
if (x_4 == 0)
{
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkEOIError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected end of input", 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_box(0);
x_5 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 4);
lean_dec(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_2, 4, x_9);
x_10 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_setPos(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_ParserState_mkErrorsAt___lambda__1(x_2, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = l_Lean_Parser_ParserState_shrinkStack(x_5, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Parser_ParserState_mkErrorsAt___lambda__1(x_2, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mkErrorsAt___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_mkErrorsAt(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_ParserState_mkErrorsAt(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_mkErrorAt(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instInhabitedPos;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1;
x_2 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_3);
x_8 = l_Lean_Parser_instInhabitedInputContext___closed__2;
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_2);
if (x_7 == 0)
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = 0;
x_11 = l_Lean_Syntax_getPos_x3f(x_5, x_10);
lean_dec(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__4;
x_13 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_12);
x_14 = l_Lean_Parser_ParserState_setPos(x_1, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 4);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_14, 4, x_17);
x_18 = l_Lean_Parser_ParserState_popSyntax(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Parser_ParserState_pushSyntax(x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 2);
x_24 = lean_ctor_get(x_14, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_9);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
x_27 = l_Lean_Parser_ParserState_popSyntax(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Parser_ParserState_pushSyntax(x_27, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = l_Lean_Parser_ParserState_setPos(x_1, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 4);
lean_dec(x_34);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_32, 4, x_11);
x_35 = l_Lean_Parser_ParserState_popSyntax(x_32);
x_36 = lean_box(0);
x_37 = l_Lean_Parser_ParserState_pushSyntax(x_35, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
x_40 = lean_ctor_get(x_32, 2);
x_41 = lean_ctor_get(x_32, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
lean_ctor_set(x_11, 0, x_9);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_11);
x_43 = l_Lean_Parser_ParserState_popSyntax(x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Parser_ParserState_pushSyntax(x_43, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
lean_dec(x_11);
x_47 = l_Lean_Parser_ParserState_setPos(x_1, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 3);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_9);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 5, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_53);
x_55 = l_Lean_Parser_ParserState_popSyntax(x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Parser_ParserState_pushSyntax(x_55, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_5);
x_58 = l_Lean_Parser_ParserState_setPos(x_1, x_3);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_58, 4);
lean_dec(x_60);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_9);
lean_ctor_set(x_58, 4, x_61);
x_62 = l_Lean_Parser_ParserState_popSyntax(x_58);
x_63 = lean_box(0);
x_64 = l_Lean_Parser_ParserState_pushSyntax(x_62, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
x_67 = lean_ctor_get(x_58, 2);
x_68 = lean_ctor_get(x_58, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_9);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set(x_70, 4, x_69);
x_71 = l_Lean_Parser_ParserState_popSyntax(x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Parser_ParserState_pushSyntax(x_71, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = l_Lean_Parser_ParserState_setPos(x_1, x_3);
x_5 = lean_box(0);
x_6 = 1;
x_7 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserFn___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserFn(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_List_appendTR___rarg(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_appendTR___rarg(x_3, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
case 3:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_List_appendTR___rarg(x_10, x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_appendTR___rarg(x_10, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_FirstTokens_toOptional(x_2);
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(1);
return x_5;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_6;
}
case 1:
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(1);
return x_7;
}
case 2:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_List_appendTR___rarg(x_8, x_10);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_List_appendTR___rarg(x_8, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_List_appendTR___rarg(x_15, x_17);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_List_appendTR___rarg(x_15, x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_22; 
x_22 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_box(1);
return x_23;
}
case 2:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = l_List_appendTR___rarg(x_24, x_26);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_List_appendTR___rarg(x_24, x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
default: 
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = l_List_appendTR___rarg(x_31, x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_List_appendTR___rarg(x_31, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_FirstTokens_toStr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_6 = lean_string_append(x_5, x_4);
x_7 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at_Lean_Parser_FirstTokens_toStr___spec__2(x_11, x_3);
x_13 = 93;
x_14 = lean_string_push(x_12, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("epsilon", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\?", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_FirstTokens_toStr___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_6);
x_8 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_Parser_FirstTokens_toStr___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_FirstTokens_toStr(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_toStr___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserInfo_collectTokens___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserInfo_collectKinds___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ParserInfo_firstTokens___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3;
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___closed__1;
x_2 = l_Lean_Parser_instInhabitedParserInfo___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Parser_info___default___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Parser_info___default___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Parser_info___default___closed__1;
x_2 = l_Lean_Parser_Parser_info___default___closed__2;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Parser_info___default___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Parser_info___default___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Parser_info___default___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParser___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___closed__3;
x_2 = l_Lean_Parser_instInhabitedParser___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_instInhabitedParser___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_apply_1(x_1, x_6);
lean_ctor_set(x_3, 2, x_7);
x_8 = lean_apply_2(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_13 = lean_apply_1(x_1, x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_apply_2(x_2, x_14, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_adaptCacheableContextFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContext___elambda__1), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContext___elambda__1), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
x_9 = lean_apply_2(x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_dec(x_13);
lean_ctor_set(x_11, 1, x_8);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_22 = x_16;
} else {
 lean_dec_ref(x_16);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_4, 0, x_27);
x_28 = lean_apply_2(x_2, x_3, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 4);
lean_inc(x_33);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 x_34 = x_28;
} else {
 lean_dec_ref(x_28);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_26);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 5, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 4, x_33);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
x_41 = lean_ctor_get(x_4, 2);
x_42 = lean_ctor_get(x_4, 3);
x_43 = lean_ctor_get(x_4, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_1);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
x_49 = lean_apply_2(x_2, x_3, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 4);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_45);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_54);
return x_59;
}
}
}
static lean_object* _init_l_Lean_Parser_withResetCacheFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_Lean_Parser_withResetCacheFn___lambda__1___closed__1;
lean_ctor_set(x_5, 1, x_8);
x_9 = lean_apply_2(x_1, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_dec(x_13);
lean_ctor_set(x_11, 1, x_7);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_9, 3, x_15);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
x_19 = lean_ctor_get(x_9, 2);
x_20 = lean_ctor_get(x_9, 4);
lean_inc(x_20);
lean_inc(x_16);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_22 = x_16;
} else {
 lean_dec_ref(x_16);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_7);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = l_Lean_Parser_withResetCacheFn___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_3, 3, x_28);
x_29 = lean_apply_2(x_1, x_2, x_3);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 4);
lean_inc(x_34);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 x_35 = x_29;
} else {
 lean_dec_ref(x_29);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_26);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 5, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_34);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_40 = lean_ctor_get(x_3, 3);
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_ctor_get(x_3, 4);
lean_inc(x_44);
lean_inc(x_40);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_3);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
x_48 = l_Lean_Parser_withResetCacheFn___lambda__1___closed__1;
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set(x_50, 4, x_44);
x_51 = lean_apply_2(x_1, x_2, x_50);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 x_57 = x_51;
} else {
 lean_dec_ref(x_51);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_46);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 5, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_56);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(x_5, x_4, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_withResetCacheFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCache___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCache___elambda__1), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Parser_withResetCacheFn(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Parser_withCacheFn___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Parser_withCacheFn___spec__5___at_Lean_Parser_withCacheFn___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_10 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_hashmap_mk_idx(x_6, x_11);
x_13 = lean_array_uget(x_1, x_12);
lean_ctor_set(x_2, 2, x_13);
x_14 = lean_array_uset(x_1, x_12, x_2);
x_1 = x_14;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_19 = lean_array_get_size(x_1);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
x_22 = lean_uint64_of_nat(x_20);
lean_dec(x_20);
x_23 = l_Lean_Name_hash___override(x_21);
lean_dec(x_21);
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = lean_hashmap_mk_idx(x_19, x_24);
x_26 = lean_array_uget(x_1, x_25);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_array_uset(x_1, x_25, x_27);
x_1 = x_28;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Parser_withCacheFn___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Lean_AssocList_foldlM___at_Lean_Parser_withCacheFn___spec__5___at_Lean_Parser_withCacheFn___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Parser_withCacheFn___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Parser_withCacheFn___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Parser_withCacheFn___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Parser_withCacheFn___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Parser_withCacheFn___spec__7(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Parser_withCacheFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_uint64_of_nat(x_8);
lean_dec(x_8);
x_11 = l_Lean_Name_hash___override(x_9);
lean_dec(x_9);
x_12 = lean_uint64_mix_hash(x_10, x_11);
lean_inc(x_7);
x_13 = lean_hashmap_mk_idx(x_7, x_12);
x_14 = lean_array_uget(x_6, x_13);
x_15 = l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_array_uset(x_6, x_13, x_18);
x_20 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_17);
x_21 = lean_nat_dec_le(x_20, x_7);
lean_dec(x_7);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_1);
x_22 = l_Lean_HashMapImp_expand___at_Lean_Parser_withCacheFn___spec__3(x_17, x_19);
return x_22;
}
else
{
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_23 = l_Lean_AssocList_replace___at_Lean_Parser_withCacheFn___spec__7(x_2, x_3, x_14);
x_24 = lean_array_uset(x_6, x_13, x_23);
lean_ctor_set(x_1, 1, x_24);
return x_1;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_uint64_of_nat(x_28);
lean_dec(x_28);
x_31 = l_Lean_Name_hash___override(x_29);
lean_dec(x_29);
x_32 = lean_uint64_mix_hash(x_30, x_31);
lean_inc(x_27);
x_33 = lean_hashmap_mk_idx(x_27, x_32);
x_34 = lean_array_uget(x_26, x_33);
x_35 = l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2(x_2, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_25, x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_34);
x_39 = lean_array_uset(x_26, x_33, x_38);
x_40 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_37);
x_41 = lean_nat_dec_le(x_40, x_27);
lean_dec(x_27);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_HashMapImp_expand___at_Lean_Parser_withCacheFn___spec__3(x_37, x_39);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
x_44 = l_Lean_AssocList_replace___at_Lean_Parser_withCacheFn___spec__7(x_2, x_3, x_34);
x_45 = lean_array_uset(x_26, x_33, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Parser_withCacheFn___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_box(0);
x_8 = 0;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_formatStxAux(x_7, x_8, x_9, x_3);
x_11 = l_Std_Format_defWidth;
x_12 = lean_format_pretty(x_10, x_11);
x_13 = lean_string_append(x_6, x_12);
lean_dec(x_12);
x_1 = x_13;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_withCacheFn___spec__8(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_formatStxAux(x_5, x_6, x_7, x_4);
x_9 = l_Std_Format_defWidth;
x_10 = lean_format_pretty(x_8, x_9);
x_11 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_formatStxAux(x_16, x_17, x_18, x_15);
x_20 = l_Std_Format_defWidth;
x_21 = lean_format_pretty(x_19, x_20);
x_22 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_List_foldl___at_Lean_Parser_withCacheFn___spec__9(x_23, x_3);
x_25 = 93;
x_26 = lean_string_push(x_24, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Parser_withCacheFn___spec__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Id_instMonadId;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Parser_withCacheFn___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Parser_withCacheFn___spec__10___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Parser_withCacheFn___spec__12(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Parser_Types_0__Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_934_(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Parser_withCacheFn___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_uint64_of_nat(x_5);
lean_dec(x_5);
x_8 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_hashmap_mk_idx(x_4, x_9);
x_11 = lean_array_uget(x_3, x_10);
lean_dec(x_3);
x_12 = l_Lean_AssocList_find_x3f___at_Lean_Parser_withCacheFn___spec__12(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_12 = l_Lean_Parser_SyntaxStack_back(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
x_14 = l_Lean_HashMap_insert___at_Lean_Parser_withCacheFn___spec__1(x_11, x_2, x_13);
lean_ctor_set(x_5, 1, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 4);
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_15);
x_21 = l_Lean_Parser_SyntaxStack_back(x_15);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
x_23 = l_Lean_HashMap_insert___at_Lean_Parser_withCacheFn___spec__1(x_20, x_2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_1, 3, x_24);
return x_1;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
lean_inc(x_25);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
lean_inc(x_26);
x_33 = l_Lean_Parser_SyntaxStack_back(x_26);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
x_35 = l_Lean_HashMap_insert___at_Lean_Parser_withCacheFn___spec__1(x_31, x_2, x_34);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_29);
return x_37;
}
}
}
static lean_object* _init_l_Lean_Parser_withCacheFn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withCacheFn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withCacheFn: unexpected stack growth ", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withCacheFn___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Parser.withCacheFn", 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
lean_inc(x_9);
x_14 = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(x_9, x_3, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_9, x_18);
lean_dec(x_9);
x_20 = lean_nat_dec_eq(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_array_to_list(lean_box(0), x_16);
x_22 = l_List_toString___at_Lean_Parser_withCacheFn___spec__8(x_21);
x_23 = l_Lean_Parser_withCacheFn___lambda__2___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_Parser_withCacheFn___lambda__2___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_Parser_SyntaxStack_back___closed__1;
x_30 = l_Lean_Parser_withCacheFn___lambda__2___closed__3;
x_31 = lean_unsigned_to_nat(422u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_28);
lean_dec(x_28);
x_34 = l_panic___at_Lean_Parser_withCacheFn___spec__10(x_33);
x_35 = l_Lean_Parser_withCacheFn___lambda__1(x_14, x_5, x_34);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
x_36 = lean_box(0);
x_37 = l_Lean_Parser_withCacheFn___lambda__1(x_14, x_5, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = l_Lean_HashMapImp_find_x3f___at_Lean_Parser_withCacheFn___spec__11(x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Parser_withCacheFn___lambda__2(x_4, x_7, x_2, x_3, x_9, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_4, 4);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 3);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Parser_SyntaxStack_push(x_6, x_21);
lean_ctor_set(x_4, 4, x_24);
lean_ctor_set(x_4, 2, x_23);
lean_ctor_set(x_4, 1, x_22);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 3);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Parser_SyntaxStack_push(x_6, x_27);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_8);
lean_ctor_set(x_32, 4, x_30);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Parser_withCacheFn___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Parser_withCacheFn___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Parser_withCacheFn___spec__12(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_withCacheFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withCacheFn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_withCacheFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_withCache___elambda__1), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_withCache___elambda__1), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_ParserFn_run___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_ParserFn_run___closed__1;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_apply_2(x_1, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = l_Lean_Parser_ParserFn_run___closed__1;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_4);
x_17 = lean_apply_2(x_1, x_16, x_5);
return x_17;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Trie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Trie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
lean_mark_persistent(l_Lean_Parser_maxPrec);
l_Lean_Parser_argPrec = _init_l_Lean_Parser_argPrec();
lean_mark_persistent(l_Lean_Parser_argPrec);
l_Lean_Parser_leadPrec = _init_l_Lean_Parser_leadPrec();
lean_mark_persistent(l_Lean_Parser_leadPrec);
l_Lean_Parser_minPrec = _init_l_Lean_Parser_minPrec();
lean_mark_persistent(l_Lean_Parser_minPrec);
l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___closed__3);
l_Lean_Parser_instInhabitedInputContext___closed__1 = _init_l_Lean_Parser_instInhabitedInputContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__1);
l_Lean_Parser_instInhabitedInputContext___closed__2 = _init_l_Lean_Parser_instInhabitedInputContext___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__2);
l_Lean_Parser_instInhabitedInputContext___closed__3 = _init_l_Lean_Parser_instInhabitedInputContext___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__3);
l_Lean_Parser_instInhabitedInputContext___closed__4 = _init_l_Lean_Parser_instInhabitedInputContext___closed__4();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__4);
l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
l_Lean_Parser_ParserModuleContext_currNamespace___default = _init_l_Lean_Parser_ParserModuleContext_currNamespace___default();
lean_mark_persistent(l_Lean_Parser_ParserModuleContext_currNamespace___default);
l_Lean_Parser_ParserModuleContext_openDecls___default = _init_l_Lean_Parser_ParserModuleContext_openDecls___default();
lean_mark_persistent(l_Lean_Parser_ParserModuleContext_openDecls___default);
l_Lean_Parser_CacheableParserContext_quotDepth___default = _init_l_Lean_Parser_CacheableParserContext_quotDepth___default();
lean_mark_persistent(l_Lean_Parser_CacheableParserContext_quotDepth___default);
l_Lean_Parser_CacheableParserContext_suppressInsideQuot___default = _init_l_Lean_Parser_CacheableParserContext_suppressInsideQuot___default();
l_Lean_Parser_CacheableParserContext_savedPos_x3f___default = _init_l_Lean_Parser_CacheableParserContext_savedPos_x3f___default();
lean_mark_persistent(l_Lean_Parser_CacheableParserContext_savedPos_x3f___default);
l_Lean_Parser_CacheableParserContext_forbiddenTk_x3f___default = _init_l_Lean_Parser_CacheableParserContext_forbiddenTk_x3f___default();
lean_mark_persistent(l_Lean_Parser_CacheableParserContext_forbiddenTk_x3f___default);
l_Lean_Parser_instBEqCacheableParserContext___closed__1 = _init_l_Lean_Parser_instBEqCacheableParserContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqCacheableParserContext___closed__1);
l_Lean_Parser_instBEqCacheableParserContext = _init_l_Lean_Parser_instBEqCacheableParserContext();
lean_mark_persistent(l_Lean_Parser_instBEqCacheableParserContext);
l_Lean_Parser_Error_unexpectedTk___default = _init_l_Lean_Parser_Error_unexpectedTk___default();
lean_mark_persistent(l_Lean_Parser_Error_unexpectedTk___default);
l_Lean_Parser_Error_unexpected___default = _init_l_Lean_Parser_Error_unexpected___default();
lean_mark_persistent(l_Lean_Parser_Error_unexpected___default);
l_Lean_Parser_Error_expected___default = _init_l_Lean_Parser_Error_expected___default();
lean_mark_persistent(l_Lean_Parser_Error_expected___default);
l_Lean_Parser_instInhabitedError___closed__1 = _init_l_Lean_Parser_instInhabitedError___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedError___closed__1);
l_Lean_Parser_instInhabitedError = _init_l_Lean_Parser_instInhabitedError();
lean_mark_persistent(l_Lean_Parser_instInhabitedError);
l_Lean_Parser_instBEqError___closed__1 = _init_l_Lean_Parser_instBEqError___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqError___closed__1);
l_Lean_Parser_instBEqError = _init_l_Lean_Parser_instBEqError();
lean_mark_persistent(l_Lean_Parser_instBEqError);
l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1 = _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1);
l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2 = _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__2);
l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1 = _init_l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1);
l_Lean_Parser_Error_toString___closed__1 = _init_l_Lean_Parser_Error_toString___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__1);
l_Lean_Parser_Error_toString___closed__2 = _init_l_Lean_Parser_Error_toString___closed__2();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__2);
l_Lean_Parser_Error_toString___closed__3 = _init_l_Lean_Parser_Error_toString___closed__3();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__3);
l_Lean_Parser_Error_toString___closed__4 = _init_l_Lean_Parser_Error_toString___closed__4();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__4);
l_Lean_Parser_Error_instToStringError___closed__1 = _init_l_Lean_Parser_Error_instToStringError___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_instToStringError___closed__1);
l_Lean_Parser_Error_instToStringError = _init_l_Lean_Parser_Error_instToStringError();
lean_mark_persistent(l_Lean_Parser_Error_instToStringError);
l_Lean_Parser_TokenCacheEntry_startPos___default = _init_l_Lean_Parser_TokenCacheEntry_startPos___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_startPos___default);
l_Lean_Parser_TokenCacheEntry_stopPos___default = _init_l_Lean_Parser_TokenCacheEntry_stopPos___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_stopPos___default);
l_Lean_Parser_TokenCacheEntry_token___default = _init_l_Lean_Parser_TokenCacheEntry_token___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_token___default);
l_Lean_Parser_instBEqParserCacheKey___closed__1 = _init_l_Lean_Parser_instBEqParserCacheKey___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqParserCacheKey___closed__1);
l_Lean_Parser_instBEqParserCacheKey = _init_l_Lean_Parser_instBEqParserCacheKey();
lean_mark_persistent(l_Lean_Parser_instBEqParserCacheKey);
l_Lean_Parser_initCacheForInput___closed__1 = _init_l_Lean_Parser_initCacheForInput___closed__1();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__1);
l_Lean_Parser_SyntaxStack_empty___closed__1 = _init_l_Lean_Parser_SyntaxStack_empty___closed__1();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_empty___closed__1);
l_Lean_Parser_SyntaxStack_empty = _init_l_Lean_Parser_SyntaxStack_empty();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_empty);
l_Lean_Parser_SyntaxStack_back___closed__1 = _init_l_Lean_Parser_SyntaxStack_back___closed__1();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__1);
l_Lean_Parser_SyntaxStack_back___closed__2 = _init_l_Lean_Parser_SyntaxStack_back___closed__2();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__2);
l_Lean_Parser_SyntaxStack_back___closed__3 = _init_l_Lean_Parser_SyntaxStack_back___closed__3();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__3);
l_Lean_Parser_SyntaxStack_back___closed__4 = _init_l_Lean_Parser_SyntaxStack_back___closed__4();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__4);
l_Lean_Parser_SyntaxStack_get_x21___closed__1 = _init_l_Lean_Parser_SyntaxStack_get_x21___closed__1();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_get_x21___closed__1);
l_Lean_Parser_SyntaxStack_get_x21___closed__2 = _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_get_x21___closed__2);
l_Lean_Parser_SyntaxStack_get_x21___closed__3 = _init_l_Lean_Parser_SyntaxStack_get_x21___closed__3();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_get_x21___closed__3);
l_Lean_Parser_ParserState_stxStack___default = _init_l_Lean_Parser_ParserState_stxStack___default();
lean_mark_persistent(l_Lean_Parser_ParserState_stxStack___default);
l_Lean_Parser_ParserState_lhsPrec___default = _init_l_Lean_Parser_ParserState_lhsPrec___default();
lean_mark_persistent(l_Lean_Parser_ParserState_lhsPrec___default);
l_Lean_Parser_ParserState_pos___default = _init_l_Lean_Parser_ParserState_pos___default();
lean_mark_persistent(l_Lean_Parser_ParserState_pos___default);
l_Lean_Parser_ParserState_errorMsg___default = _init_l_Lean_Parser_ParserState_errorMsg___default();
lean_mark_persistent(l_Lean_Parser_ParserState_errorMsg___default);
l_Lean_Parser_ParserState_mkEOIError___closed__1 = _init_l_Lean_Parser_ParserState_mkEOIError___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_mkEOIError___closed__1);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__4 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__4();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__4);
l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1 = _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1);
l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2 = _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2);
l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3 = _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3);
l_Lean_Parser_FirstTokens_toStr___closed__1 = _init_l_Lean_Parser_FirstTokens_toStr___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__1);
l_Lean_Parser_FirstTokens_toStr___closed__2 = _init_l_Lean_Parser_FirstTokens_toStr___closed__2();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__2);
l_Lean_Parser_FirstTokens_toStr___closed__3 = _init_l_Lean_Parser_FirstTokens_toStr___closed__3();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__3);
l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1 = _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1);
l_Lean_Parser_FirstTokens_instToStringFirstTokens = _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToStringFirstTokens);
l_Lean_Parser_ParserInfo_firstTokens___default = _init_l_Lean_Parser_ParserInfo_firstTokens___default();
lean_mark_persistent(l_Lean_Parser_ParserInfo_firstTokens___default);
l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1 = _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1);
l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2 = _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2);
l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3 = _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3);
l_Lean_Parser_instInhabitedParserInfo___closed__1 = _init_l_Lean_Parser_instInhabitedParserInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___closed__1);
l_Lean_Parser_instInhabitedParserInfo___closed__2 = _init_l_Lean_Parser_instInhabitedParserInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___closed__2);
l_Lean_Parser_instInhabitedParserInfo___closed__3 = _init_l_Lean_Parser_instInhabitedParserInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___closed__3);
l_Lean_Parser_instInhabitedParserInfo = _init_l_Lean_Parser_instInhabitedParserInfo();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo);
l_Lean_Parser_Parser_info___default___closed__1 = _init_l_Lean_Parser_Parser_info___default___closed__1();
lean_mark_persistent(l_Lean_Parser_Parser_info___default___closed__1);
l_Lean_Parser_Parser_info___default___closed__2 = _init_l_Lean_Parser_Parser_info___default___closed__2();
lean_mark_persistent(l_Lean_Parser_Parser_info___default___closed__2);
l_Lean_Parser_Parser_info___default___closed__3 = _init_l_Lean_Parser_Parser_info___default___closed__3();
lean_mark_persistent(l_Lean_Parser_Parser_info___default___closed__3);
l_Lean_Parser_Parser_info___default = _init_l_Lean_Parser_Parser_info___default();
lean_mark_persistent(l_Lean_Parser_Parser_info___default);
l_Lean_Parser_instInhabitedParser___closed__1 = _init_l_Lean_Parser_instInhabitedParser___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__1);
l_Lean_Parser_instInhabitedParser___closed__2 = _init_l_Lean_Parser_instInhabitedParser___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__2);
l_Lean_Parser_instInhabitedParser = _init_l_Lean_Parser_instInhabitedParser();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser);
l_Lean_Parser_withResetCacheFn___lambda__1___closed__1 = _init_l_Lean_Parser_withResetCacheFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_withResetCacheFn___lambda__1___closed__1);
l_panic___at_Lean_Parser_withCacheFn___spec__10___closed__1 = _init_l_panic___at_Lean_Parser_withCacheFn___spec__10___closed__1();
lean_mark_persistent(l_panic___at_Lean_Parser_withCacheFn___spec__10___closed__1);
l_Lean_Parser_withCacheFn___lambda__2___closed__1 = _init_l_Lean_Parser_withCacheFn___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_withCacheFn___lambda__2___closed__1);
l_Lean_Parser_withCacheFn___lambda__2___closed__2 = _init_l_Lean_Parser_withCacheFn___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_withCacheFn___lambda__2___closed__2);
l_Lean_Parser_withCacheFn___lambda__2___closed__3 = _init_l_Lean_Parser_withCacheFn___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_withCacheFn___lambda__2___closed__3);
l_Lean_Parser_ParserFn_run___closed__1 = _init_l_Lean_Parser_ParserFn_run___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserFn_run___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
