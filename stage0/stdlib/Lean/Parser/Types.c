// Lean compiler output
// Module: Lean.Parser.Types
// Imports: Lean.Data.Trie Lean.Syntax Lean.Message Lean.DocString.Extension
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_instToString___closed__0;
static lean_object* l_Lean_Parser_SyntaxStack_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserFn_run___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__0;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_empty;
static lean_object* l_Lean_Parser_instBEqParserCacheKey___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey;
static lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_instToString;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__1;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey;
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__0(lean_object*);
static lean_object* l_Lean_Parser_initCacheForInput___closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245____boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__1;
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_empty___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_instToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
static lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_allErrors___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initCacheForInput___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0;
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
static lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__4;
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instBEqCacheableParserContext___closed__0;
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__0;
static lean_object* l_Lean_Parser_instInhabitedParser___closed__4;
LEAN_EXPORT uint8_t l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__0;
static lean_object* l_Lean_Parser_initCacheForInput___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__2;
LEAN_EXPORT uint8_t l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initCacheForInput___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedInputContext;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedError;
static lean_object* l_Lean_Parser_initCacheForInput___closed__3;
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3;
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
uint8_t l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_argPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__0;
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_List_eraseRepsBy___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
uint8_t l_List_beq___at___Lean_Syntax_beqPreresolved____x40_Init_Meta___hyg_2739__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__0;
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___System_FilePath_parent_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_allErrors___closed__0;
static lean_object* l_Lean_Parser_instInhabitedParser___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError;
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instBEqError___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_SearchPath_findAllWithExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__3;
static lean_object* l_Lean_Parser_initCacheForInput___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__3;
static lean_object* l_Lean_Parser_instInhabitedError___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_minPrec;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_instToString;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadPrec;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedFirstTokens;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__1;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_17; 
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
x_17 = lean_nat_dec_eq(x_3, x_8);
if (x_17 == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_4, x_9);
if (x_18 == 0)
{
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
if (x_5 == 0)
{
if (x_10 == 0)
{
x_13 = x_18;
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = lean_unbox(x_19);
return x_20;
}
}
else
{
if (x_10 == 0)
{
uint8_t x_21; 
x_21 = lean_unbox(x_19);
return x_21;
}
else
{
x_13 = x_18;
goto block_16;
}
}
}
}
block_16:
{
if (x_13 == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___System_FilePath_parent_spec__0(x_6, x_11);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_SearchPath_findAllWithExt_spec__0(x_7, x_12);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqCacheableParserContext___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedError___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedError___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478_(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_string_dec_eq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_List_beq___at___Lean_Syntax_beqPreresolved____x40_Init_Meta___hyg_2739__spec__0(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqError___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" or ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__0;
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
x_8 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0;
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
x_12 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
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
LEAN_EXPORT uint8_t l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0___lam__0___boxed), 2, 0);
x_3 = l_List_eraseRepsBy___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("; ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_47; uint8_t x_48; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec(x_1);
x_47 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_48 = lean_string_dec_eq(x_34, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_49);
x_36 = x_50;
goto block_46;
}
else
{
lean_object* x_51; 
lean_dec(x_34);
x_51 = lean_box(0);
x_36 = x_51;
goto block_46;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_Error_toString___closed__0;
x_5 = l_List_appendTR___redArg(x_2, x_3);
x_6 = l_String_intercalate(x_4, x_5);
return x_6;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_to_list(x_10);
x_12 = l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0(x_11);
x_13 = l_Lean_Parser_Error_toString___closed__1;
x_14 = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(x_12);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_2 = x_9;
x_3 = x_16;
goto block_7;
}
block_25:
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(x_20, x_19, x_23);
lean_dec(x_23);
x_8 = x_18;
x_9 = x_22;
x_10 = x_24;
goto block_17;
}
block_33:
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_31, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_inc(x_31);
x_18 = x_26;
x_19 = x_31;
x_20 = x_28;
x_21 = x_27;
x_22 = x_29;
x_23 = x_31;
goto block_25;
}
else
{
x_18 = x_26;
x_19 = x_31;
x_20 = x_28;
x_21 = x_27;
x_22 = x_29;
x_23 = x_30;
goto block_25;
}
}
block_46:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(0);
x_38 = l_List_beq___at___Lean_Syntax_beqPreresolved____x40_Init_Meta___hyg_2739__spec__0(x_35, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_array_mk(x_35);
x_40 = lean_array_get_size(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_40, x_43);
x_45 = lean_nat_dec_le(x_41, x_44);
if (x_45 == 0)
{
lean_inc(x_44);
x_26 = x_37;
x_27 = x_40;
x_28 = x_39;
x_29 = x_36;
x_30 = x_44;
x_31 = x_44;
goto block_33;
}
else
{
x_26 = x_37;
x_27 = x_40;
x_28 = x_39;
x_29 = x_36;
x_30 = x_44;
x_31 = x_41;
goto block_33;
}
}
else
{
lean_dec(x_40);
x_8 = x_37;
x_9 = x_36;
x_10 = x_39;
goto block_17;
}
}
else
{
lean_dec(x_35);
x_2 = x_36;
x_3 = x_37;
goto block_7;
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_eraseReps___at___Lean_Parser_Error_toString_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_Parser_Error_toString_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Error_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Error_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_instToString___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_16 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_17 = lean_string_dec_eq(x_4, x_16);
if (x_17 == 0)
{
x_6 = x_4;
goto block_15;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_6 = x_18;
goto block_15;
}
block_15:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = l_List_appendTR___redArg(x_8, x_5);
lean_ctor_set(x_1, 2, x_11);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_List_appendTR___redArg(x_12, x_5);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = l_Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_245_(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_name_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqParserCacheKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqParserCacheKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqParserCacheKey___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_uint64_of_nat(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instHashableParserCacheKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_instHashableParserCacheKey___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Parser_initCacheForInput___closed__1;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initCacheForInput___closed__2;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initCacheForInput___closed__3;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initCacheForInput___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_Lean_Parser_initCacheForInput___closed__0;
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Lean_Parser_initCacheForInput___closed__5;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
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
x_5 = l_Array_toSubarray___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_empty___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Parser_SyntaxStack_empty___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
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
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
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
x_7 = l_Array_shrink___redArg(x_4, x_6);
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
x_11 = l_Array_shrink___redArg(x_8, x_10);
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
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_SyntaxStack_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Parser.Types", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Parser.SyntaxStack.back", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SyntaxStack.back: element is inaccessible", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_SyntaxStack_back___closed__2;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(176u);
x_4 = l_Lean_Parser_SyntaxStack_back___closed__1;
x_5 = l_Lean_Parser_SyntaxStack_back___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_SyntaxStack_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_SyntaxStack_back___closed__3;
x_6 = l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_box(0);
x_9 = l_Array_back_x21___redArg(x_8, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_SyntaxStack_back(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Parser.SyntaxStack.get!", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SyntaxStack.get!: element is inaccessible", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_SyntaxStack_get_x21___closed__1;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(182u);
x_4 = l_Lean_Parser_SyntaxStack_get_x21___closed__0;
x_5 = l_Lean_Parser_SyntaxStack_back___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
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
x_5 = l_Lean_Parser_SyntaxStack_get_x21___closed__2;
x_6 = l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_8, x_2);
x_11 = lean_array_get(x_9, x_7, x_10);
lean_dec(x_10);
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
x_8 = l_Array_extract___redArg(x_4, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Array_append___redArg(x_4, x_2);
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
x_8 = l_Array_append___redArg(x_6, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_instHAppendArraySyntax() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Parser_instBEqError___closed__0;
x_4 = lean_box(0);
x_5 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(x_3, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_14 = l_Lean_Parser_SyntaxStack_shrink(x_10, x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_13);
return x_16;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
return x_10;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_2);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
return x_10;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = l_Lean_Parser_SyntaxStack_push(x_6, x_2);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
return x_13;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_11 = l_Lean_Parser_SyntaxStack_pop(x_5);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set(x_12, 5, x_10);
return x_12;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = l_Lean_Parser_SyntaxStack_shrink(x_6, x_2);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
return x_13;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = lean_string_utf8_next(x_2, x_3);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_string_utf8_next_fast(x_2, x_3);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_next_x27___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_next_x27___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_478_(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_10 = x_1;
} else {
 lean_dec_ref(x_1);
 x_10 = lean_box(0);
}
x_19 = lean_box(0);
lean_inc(x_8);
x_20 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Parser_SyntaxStack_size(x_4);
x_22 = lean_nat_dec_eq(x_21, x_3);
lean_dec(x_21);
if (x_22 == 0)
{
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = l_Lean_Parser_SyntaxStack_push(x_4, x_23);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_8);
lean_ctor_set(x_25, 5, x_9);
return x_25;
}
}
else
{
goto block_18;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_box(2);
x_12 = l_Lean_Parser_SyntaxStack_size(x_4);
x_13 = l_Lean_Parser_SyntaxStack_extract(x_4, x_3, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Parser_SyntaxStack_shrink(x_4, x_3);
x_16 = l_Lean_Parser_SyntaxStack_push(x_15, x_14);
if (lean_is_scalar(x_10)) {
 x_17 = lean_alloc_ctor(0, 6, 0);
} else {
 x_17 = x_10;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set(x_17, 4, x_8);
lean_ctor_set(x_17, 5, x_9);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
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
x_6 = lean_box(2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
x_9 = l_Lean_Parser_SyntaxStack_size(x_5);
x_10 = l_Lean_Parser_SyntaxStack_extract(x_5, x_8, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_Parser_SyntaxStack_shrink(x_5, x_8);
lean_dec(x_8);
x_13 = l_Lean_Parser_SyntaxStack_push(x_12, x_11);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_ctor_get(x_1, 4);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_20 = lean_box(2);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_3, x_21);
x_23 = l_Lean_Parser_SyntaxStack_size(x_14);
x_24 = l_Lean_Parser_SyntaxStack_extract(x_14, x_22, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_SyntaxStack_shrink(x_14, x_22);
lean_dec(x_22);
x_27 = l_Lean_Parser_SyntaxStack_push(x_26, x_25);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_16);
lean_ctor_set(x_28, 3, x_17);
lean_ctor_set(x_28, 4, x_18);
lean_ctor_set(x_28, 5, x_19);
return x_28;
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
static lean_object* _init_l_Lean_Parser_ParserState_allErrors___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_allErrors___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Parser_ParserState_allErrors___closed__0;
x_5 = l_Array_append___redArg(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_ParserState_allErrors___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Array_append___redArg(x_8, x_13);
lean_dec(x_13);
return x_14;
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_11);
lean_ctor_set(x_12, 5, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 4);
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_1, 4, x_10);
x_11 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_16);
x_24 = l_Lean_Parser_ParserState_pushSyntax(x_23, x_17);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 4);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 4, x_9);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_7);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_15);
if (x_4 == 0)
{
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_16);
return x_20;
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
static lean_object* _init_l_Lean_Parser_ParserState_mkEOIError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_ParserState_mkEOIError___closed__0;
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_25; 
x_25 = l_Lean_Parser_ParserState_setPos(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
x_5 = x_25;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = l_Lean_Parser_ParserState_shrinkStack(x_25, x_26);
x_5 = x_27;
goto block_24;
}
block_24:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 4);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 4, x_11);
x_12 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_17);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_22, x_18);
return x_23;
}
}
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1;
x_5 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_29; uint8_t x_30; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
lean_dec(x_4);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_3);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_3);
x_31 = l_Lean_Syntax_getPos_x3f(x_5, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3;
x_33 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_32);
x_6 = x_33;
goto block_28;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_6 = x_34;
goto block_28;
}
}
else
{
x_6 = x_3;
goto block_28;
}
block_28:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Parser_ParserState_setPos(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 4);
lean_dec(x_9);
x_10 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 4, x_12);
x_13 = l_Lean_Parser_ParserState_popSyntax(x_7);
x_14 = lean_box(0);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_ctor_get(x_7, 2);
x_19 = lean_ctor_get(x_7, 3);
x_20 = lean_ctor_get(x_7, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_21 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_23);
lean_ctor_set(x_24, 5, x_20);
x_25 = l_Lean_Parser_ParserState_popSyntax(x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Parser_ParserState_pushSyntax(x_25, x_26);
return x_27;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = l_Lean_Parser_ParserState_setPos(x_1, x_3);
x_5 = lean_box(0);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_5, x_7);
return x_8;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_26; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_26 = lean_string_dec_eq(x_6, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0;
x_28 = lean_string_append(x_6, x_27);
x_12 = x_28;
goto block_25;
}
else
{
x_12 = x_6;
goto block_25;
}
block_25:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = l_Lean_FileMap_toPosition(x_14, x_10);
lean_dec(x_10);
x_16 = l_Lean_Parser_Error_toString(x_11);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lean_mkErrorStringWithPos(x_13, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_16);
x_21 = lean_string_append(x_12, x_20);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_instInhabitedInputContext___closed__0;
x_4 = l_Lean_Parser_ParserState_allErrors(x_2);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0(x_1, x_3, x_4, x_5, x_6, x_3);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserFn() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_instInhabitedParserFn___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
x_6 = l_List_appendTR___redArg(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_appendTR___redArg(x_3, x_7);
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
x_13 = l_List_appendTR___redArg(x_10, x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_appendTR___redArg(x_10, x_14);
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
lean_object* x_3; lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_FirstTokens_toOptional(x_2);
return x_8;
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_9;
}
case 1:
{
return x_2;
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_10;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_List_appendTR___redArg(x_11, x_13);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_List_appendTR___redArg(x_11, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
default: 
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_3 = x_18;
x_4 = x_19;
goto block_7;
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_20; 
x_20 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_20;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_3 = x_21;
x_4 = x_22;
goto block_7;
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_appendTR___redArg(x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("epsilon", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\?", 1, 1);
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
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_FirstTokens_toStr___closed__1;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_Parser_FirstTokens_toStr___closed__2;
x_8 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_6);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
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
static lean_object* _init_l_Lean_Parser_FirstTokens_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_toStr___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_FirstTokens_instToString___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lam__1___boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_instInhabitedParser___closed__2;
x_3 = l_Lean_Parser_instInhabitedParser___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__0;
x_2 = l_Lean_Parser_instInhabitedParser___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__4;
return x_1;
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
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_8);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_4, 0, x_28);
x_29 = lean_apply_2(x_2, x_3, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 5);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_27);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 6, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_34);
lean_ctor_set(x_40, 5, x_35);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
x_43 = lean_ctor_get(x_4, 2);
x_44 = lean_ctor_get(x_4, 3);
x_45 = lean_ctor_get(x_4, 4);
x_46 = lean_ctor_get(x_4, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_1);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set(x_51, 4, x_45);
lean_ctor_set(x_51, 5, x_46);
x_52 = lean_apply_2(x_2, x_3, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_48);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_55);
lean_ctor_set(x_63, 3, x_56);
lean_ctor_set(x_63, 4, x_57);
lean_ctor_set(x_63, 5, x_58);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Parser_initCacheForInput___closed__5;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
x_19 = lean_ctor_get(x_9, 2);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_16);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = l_Lean_Parser_initCacheForInput___closed__5;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_3, 3, x_29);
x_30 = lean_apply_2(x_1, x_2, x_3);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 5);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_27);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 6, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_42 = lean_ctor_get(x_3, 3);
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get(x_3, 4);
x_47 = lean_ctor_get(x_3, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
x_51 = l_Lean_Parser_initCacheForInput___closed__5;
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_46);
lean_ctor_set(x_53, 5, x_47);
x_54 = lean_apply_2(x_1, x_2, x_53);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 5);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_49);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 6, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 4, x_59);
lean_ctor_set(x_65, 5, x_60);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(x_5, x_4, x_2, x_3);
return x_6;
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Parser_withResetCacheFn(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_10 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_array_get_size(x_1);
x_32 = lean_uint64_of_nat(x_30);
lean_dec(x_30);
x_33 = l_Lean_Name_hash___override(x_29);
lean_dec(x_29);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_Parser_beqParserCacheKey____x40_Lean_Parser_Types___hyg_857_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 4);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_9);
x_16 = lean_array_get_size(x_13);
x_17 = lean_uint64_of_nat(x_9);
x_18 = l_Lean_Name_hash___override(x_1);
lean_dec(x_1);
x_19 = lean_uint64_mix_hash(x_17, x_18);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_13, x_30);
lean_dec(x_13);
x_32 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg(x_15, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_box(0);
lean_ctor_set(x_4, 4, x_36);
lean_ctor_set(x_4, 1, x_35);
lean_inc(x_3);
x_37 = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(x_34, x_2, x_3, x_4);
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_57; 
x_39 = lean_ctor_get(x_3, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_3, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_3, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_3, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_37, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_37, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_49 = x_37;
} else {
 lean_dec_ref(x_37);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
x_60 = l_Lean_Parser_SyntaxStack_back(x_44);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_ctor_set(x_3, 3, x_47);
lean_ctor_set(x_3, 2, x_46);
lean_ctor_set(x_3, 1, x_45);
lean_ctor_set(x_3, 0, x_60);
x_61 = lean_array_get_size(x_59);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = lean_usize_sub(x_62, x_28);
x_64 = lean_usize_land(x_26, x_63);
x_65 = lean_array_uget(x_59, x_64);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(x_15, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_58, x_67);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_15);
lean_ctor_set(x_69, 1, x_3);
lean_ctor_set(x_69, 2, x_65);
x_70 = lean_array_uset(x_59, x_64, x_69);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_nat_mul(x_68, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(x_70);
lean_ctor_set(x_51, 1, x_77);
lean_ctor_set(x_51, 0, x_68);
x_53 = x_51;
goto block_56;
}
else
{
lean_ctor_set(x_51, 1, x_70);
lean_ctor_set(x_51, 0, x_68);
x_53 = x_51;
goto block_56;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_box(0);
x_79 = lean_array_uset(x_59, x_64, x_78);
x_80 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_15, x_3, x_65);
x_81 = lean_array_uset(x_79, x_64, x_80);
lean_ctor_set(x_51, 1, x_81);
x_53 = x_51;
goto block_56;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; size_t x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_ctor_get(x_51, 0);
x_83 = lean_ctor_get(x_51, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_51);
x_84 = l_Lean_Parser_SyntaxStack_back(x_44);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_ctor_set(x_3, 3, x_47);
lean_ctor_set(x_3, 2, x_46);
lean_ctor_set(x_3, 1, x_45);
lean_ctor_set(x_3, 0, x_84);
x_85 = lean_array_get_size(x_83);
x_86 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_87 = lean_usize_sub(x_86, x_28);
x_88 = lean_usize_land(x_26, x_87);
x_89 = lean_array_uget(x_83, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(x_15, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_82, x_91);
lean_dec(x_82);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_15);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 2, x_89);
x_94 = lean_array_uset(x_83, x_88, x_93);
x_95 = lean_unsigned_to_nat(4u);
x_96 = lean_nat_mul(x_92, x_95);
x_97 = lean_unsigned_to_nat(3u);
x_98 = lean_nat_div(x_96, x_97);
lean_dec(x_96);
x_99 = lean_array_get_size(x_94);
x_100 = lean_nat_dec_le(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(x_94);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_92);
lean_ctor_set(x_102, 1, x_101);
x_53 = x_102;
goto block_56;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_94);
x_53 = x_103;
goto block_56;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_box(0);
x_105 = lean_array_uset(x_83, x_88, x_104);
x_106 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_15, x_3, x_89);
x_107 = lean_array_uset(x_105, x_88, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_82);
lean_ctor_set(x_108, 1, x_107);
x_53 = x_108;
goto block_56;
}
}
block_56:
{
lean_object* x_54; lean_object* x_55; 
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(0, 6, 0);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_47);
lean_ctor_set(x_55, 5, x_48);
return x_55;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; size_t x_129; size_t x_130; size_t x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_3);
x_109 = lean_ctor_get(x_37, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_37, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_37, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_37, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_37, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_37, 5);
lean_inc(x_114);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_115 = x_37;
} else {
 lean_dec_ref(x_37);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
x_123 = lean_ctor_get(x_117, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_125 = x_117;
} else {
 lean_dec_ref(x_117);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Parser_SyntaxStack_back(x_110);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_111);
lean_ctor_set(x_127, 2, x_112);
lean_ctor_set(x_127, 3, x_113);
x_128 = lean_array_get_size(x_124);
x_129 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_130 = lean_usize_sub(x_129, x_28);
x_131 = lean_usize_land(x_26, x_130);
x_132 = lean_array_uget(x_124, x_131);
x_133 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(x_15, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_add(x_123, x_134);
lean_dec(x_123);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_15);
lean_ctor_set(x_136, 1, x_127);
lean_ctor_set(x_136, 2, x_132);
x_137 = lean_array_uset(x_124, x_131, x_136);
x_138 = lean_unsigned_to_nat(4u);
x_139 = lean_nat_mul(x_135, x_138);
x_140 = lean_unsigned_to_nat(3u);
x_141 = lean_nat_div(x_139, x_140);
lean_dec(x_139);
x_142 = lean_array_get_size(x_137);
x_143 = lean_nat_dec_le(x_141, x_142);
lean_dec(x_142);
lean_dec(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(x_137);
if (lean_is_scalar(x_125)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_125;
}
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
x_119 = x_145;
goto block_122;
}
else
{
lean_object* x_146; 
if (lean_is_scalar(x_125)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_125;
}
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_137);
x_119 = x_146;
goto block_122;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_box(0);
x_148 = lean_array_uset(x_124, x_131, x_147);
x_149 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_15, x_127, x_132);
x_150 = lean_array_uset(x_148, x_131, x_149);
if (lean_is_scalar(x_125)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_125;
}
lean_ctor_set(x_151, 0, x_123);
lean_ctor_set(x_151, 1, x_150);
x_119 = x_151;
goto block_122;
}
block_122:
{
lean_object* x_120; lean_object* x_121; 
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_115)) {
 x_121 = lean_alloc_ctor(0, 6, 0);
} else {
 x_121 = x_115;
}
lean_ctor_set(x_121, 0, x_110);
lean_ctor_set(x_121, 1, x_111);
lean_ctor_set(x_121, 2, x_112);
lean_ctor_set(x_121, 3, x_120);
lean_ctor_set(x_121, 4, x_113);
lean_ctor_set(x_121, 5, x_114);
return x_121;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_ctor_get(x_32, 0);
lean_inc(x_152);
lean_dec(x_32);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 3);
lean_inc(x_156);
lean_dec(x_152);
x_157 = l_Lean_Parser_SyntaxStack_push(x_8, x_153);
lean_ctor_set(x_4, 4, x_156);
lean_ctor_set(x_4, 2, x_155);
lean_ctor_set(x_4, 1, x_154);
lean_ctor_set(x_4, 0, x_157);
return x_4;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; size_t x_174; size_t x_175; size_t x_176; size_t x_177; size_t x_178; lean_object* x_179; lean_object* x_180; 
x_158 = lean_ctor_get(x_4, 0);
x_159 = lean_ctor_get(x_4, 2);
x_160 = lean_ctor_get(x_4, 5);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_4);
x_161 = lean_ctor_get(x_6, 1);
lean_inc(x_161);
lean_dec(x_6);
x_162 = lean_ctor_get(x_3, 2);
lean_inc(x_162);
lean_inc(x_159);
lean_inc(x_1);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_1);
lean_ctor_set(x_163, 2, x_159);
x_164 = lean_array_get_size(x_161);
x_165 = lean_uint64_of_nat(x_159);
x_166 = l_Lean_Name_hash___override(x_1);
lean_dec(x_1);
x_167 = lean_uint64_mix_hash(x_165, x_166);
x_168 = 32;
x_169 = lean_uint64_shift_right(x_167, x_168);
x_170 = lean_uint64_xor(x_167, x_169);
x_171 = 16;
x_172 = lean_uint64_shift_right(x_170, x_171);
x_173 = lean_uint64_xor(x_170, x_172);
x_174 = lean_uint64_to_usize(x_173);
x_175 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_176 = 1;
x_177 = lean_usize_sub(x_175, x_176);
x_178 = lean_usize_land(x_174, x_177);
x_179 = lean_array_uget(x_161, x_178);
lean_dec(x_161);
x_180 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg(x_163, x_179);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; size_t x_208; size_t x_209; size_t x_210; lean_object* x_211; uint8_t x_212; 
x_181 = lean_ctor_get(x_158, 0);
lean_inc(x_181);
x_182 = lean_array_get_size(x_181);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_158);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_159);
lean_ctor_set(x_185, 3, x_5);
lean_ctor_set(x_185, 4, x_184);
lean_ctor_set(x_185, 5, x_160);
lean_inc(x_3);
x_186 = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(x_182, x_2, x_3, x_185);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_187 = x_3;
} else {
 lean_dec_ref(x_3);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_186, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_188, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
x_202 = lean_ctor_get(x_196, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_204 = x_196;
} else {
 lean_dec_ref(x_196);
 x_204 = lean_box(0);
}
x_205 = l_Lean_Parser_SyntaxStack_back(x_189);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
if (lean_is_scalar(x_187)) {
 x_206 = lean_alloc_ctor(0, 4, 0);
} else {
 x_206 = x_187;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_190);
lean_ctor_set(x_206, 2, x_191);
lean_ctor_set(x_206, 3, x_192);
x_207 = lean_array_get_size(x_203);
x_208 = lean_usize_of_nat(x_207);
lean_dec(x_207);
x_209 = lean_usize_sub(x_208, x_176);
x_210 = lean_usize_land(x_174, x_209);
x_211 = lean_array_uget(x_203, x_210);
x_212 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(x_163, x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_202, x_213);
lean_dec(x_202);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_163);
lean_ctor_set(x_215, 1, x_206);
lean_ctor_set(x_215, 2, x_211);
x_216 = lean_array_uset(x_203, x_210, x_215);
x_217 = lean_unsigned_to_nat(4u);
x_218 = lean_nat_mul(x_214, x_217);
x_219 = lean_unsigned_to_nat(3u);
x_220 = lean_nat_div(x_218, x_219);
lean_dec(x_218);
x_221 = lean_array_get_size(x_216);
x_222 = lean_nat_dec_le(x_220, x_221);
lean_dec(x_221);
lean_dec(x_220);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Parser_withCacheFn_spec__2___redArg(x_216);
if (lean_is_scalar(x_204)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_204;
}
lean_ctor_set(x_224, 0, x_214);
lean_ctor_set(x_224, 1, x_223);
x_198 = x_224;
goto block_201;
}
else
{
lean_object* x_225; 
if (lean_is_scalar(x_204)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_204;
}
lean_ctor_set(x_225, 0, x_214);
lean_ctor_set(x_225, 1, x_216);
x_198 = x_225;
goto block_201;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_box(0);
x_227 = lean_array_uset(x_203, x_210, x_226);
x_228 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Parser_withCacheFn_spec__5___redArg(x_163, x_206, x_211);
x_229 = lean_array_uset(x_227, x_210, x_228);
if (lean_is_scalar(x_204)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_204;
}
lean_ctor_set(x_230, 0, x_202);
lean_ctor_set(x_230, 1, x_229);
x_198 = x_230;
goto block_201;
}
block_201:
{
lean_object* x_199; lean_object* x_200; 
if (lean_is_scalar(x_197)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_197;
}
lean_ctor_set(x_199, 0, x_195);
lean_ctor_set(x_199, 1, x_198);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_194;
}
lean_ctor_set(x_200, 0, x_189);
lean_ctor_set(x_200, 1, x_190);
lean_ctor_set(x_200, 2, x_191);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_200, 4, x_192);
lean_ctor_set(x_200, 5, x_193);
return x_200;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_163);
lean_dec(x_159);
lean_dec(x_3);
lean_dec(x_2);
x_231 = lean_ctor_get(x_180, 0);
lean_inc(x_231);
lean_dec(x_180);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 2);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 3);
lean_inc(x_235);
lean_dec(x_231);
x_236 = l_Lean_Parser_SyntaxStack_push(x_158, x_232);
x_237 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_233);
lean_ctor_set(x_237, 2, x_234);
lean_ctor_set(x_237, 3, x_5);
lean_ctor_set(x_237, 4, x_235);
lean_ctor_set(x_237, 5, x_160);
return x_237;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Parser_withCacheFn_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Parser_withCacheFn_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withCache", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2;
x_2 = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1;
x_3 = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Run `p` and record result in parser cache for any further invocation with this `parserName`, parser context, and parser state.\n`p` cannot access syntax stack elements pushed before the invocation in order to make caching independent of parser history.\nAs this excludes trailing parsers from being cached, we also reset `lhsPrec`, which is not read but set by leading parsers, to 0\nin order to increase cache hits. Finally, `errorMsg` is also reset to `none` as a leading parser should not be called in the first\nplace if there was an error.\n", 541, 541);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__3;
x_3 = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__4;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
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
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_ParserFn_run___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ParserFn_run___closed__0;
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_4);
x_8 = lean_apply_2(x_1, x_7, x_5);
return x_8;
}
}
lean_object* initialize_Lean_Data_Trie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Trie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin, lean_io_mk_world());
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
l_Lean_Parser_instInhabitedInputContext___closed__0 = _init_l_Lean_Parser_instInhabitedInputContext___closed__0();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__0);
l_Lean_Parser_instInhabitedInputContext___closed__1 = _init_l_Lean_Parser_instInhabitedInputContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__1);
l_Lean_Parser_instInhabitedInputContext___closed__2 = _init_l_Lean_Parser_instInhabitedInputContext___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__2);
l_Lean_Parser_instInhabitedInputContext___closed__3 = _init_l_Lean_Parser_instInhabitedInputContext___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__3);
l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
l_Lean_Parser_instBEqCacheableParserContext___closed__0 = _init_l_Lean_Parser_instBEqCacheableParserContext___closed__0();
lean_mark_persistent(l_Lean_Parser_instBEqCacheableParserContext___closed__0);
l_Lean_Parser_instBEqCacheableParserContext = _init_l_Lean_Parser_instBEqCacheableParserContext();
lean_mark_persistent(l_Lean_Parser_instBEqCacheableParserContext);
l_Lean_Parser_instInhabitedError___closed__0 = _init_l_Lean_Parser_instInhabitedError___closed__0();
lean_mark_persistent(l_Lean_Parser_instInhabitedError___closed__0);
l_Lean_Parser_instInhabitedError = _init_l_Lean_Parser_instInhabitedError();
lean_mark_persistent(l_Lean_Parser_instInhabitedError);
l_Lean_Parser_instBEqError___closed__0 = _init_l_Lean_Parser_instBEqError___closed__0();
lean_mark_persistent(l_Lean_Parser_instBEqError___closed__0);
l_Lean_Parser_instBEqError = _init_l_Lean_Parser_instBEqError();
lean_mark_persistent(l_Lean_Parser_instBEqError);
l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0 = _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0();
lean_mark_persistent(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0);
l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1 = _init_l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1);
l_Lean_Parser_Error_toString___closed__0 = _init_l_Lean_Parser_Error_toString___closed__0();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__0);
l_Lean_Parser_Error_toString___closed__1 = _init_l_Lean_Parser_Error_toString___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__1);
l_Lean_Parser_Error_instToString___closed__0 = _init_l_Lean_Parser_Error_instToString___closed__0();
lean_mark_persistent(l_Lean_Parser_Error_instToString___closed__0);
l_Lean_Parser_Error_instToString = _init_l_Lean_Parser_Error_instToString();
lean_mark_persistent(l_Lean_Parser_Error_instToString);
l_Lean_Parser_instBEqParserCacheKey___closed__0 = _init_l_Lean_Parser_instBEqParserCacheKey___closed__0();
lean_mark_persistent(l_Lean_Parser_instBEqParserCacheKey___closed__0);
l_Lean_Parser_instBEqParserCacheKey = _init_l_Lean_Parser_instBEqParserCacheKey();
lean_mark_persistent(l_Lean_Parser_instBEqParserCacheKey);
l_Lean_Parser_instHashableParserCacheKey = _init_l_Lean_Parser_instHashableParserCacheKey();
lean_mark_persistent(l_Lean_Parser_instHashableParserCacheKey);
l_Lean_Parser_initCacheForInput___closed__0 = _init_l_Lean_Parser_initCacheForInput___closed__0();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__0);
l_Lean_Parser_initCacheForInput___closed__1 = _init_l_Lean_Parser_initCacheForInput___closed__1();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__1);
l_Lean_Parser_initCacheForInput___closed__2 = _init_l_Lean_Parser_initCacheForInput___closed__2();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__2);
l_Lean_Parser_initCacheForInput___closed__3 = _init_l_Lean_Parser_initCacheForInput___closed__3();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__3);
l_Lean_Parser_initCacheForInput___closed__4 = _init_l_Lean_Parser_initCacheForInput___closed__4();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__4);
l_Lean_Parser_initCacheForInput___closed__5 = _init_l_Lean_Parser_initCacheForInput___closed__5();
lean_mark_persistent(l_Lean_Parser_initCacheForInput___closed__5);
l_Lean_Parser_SyntaxStack_empty___closed__0 = _init_l_Lean_Parser_SyntaxStack_empty___closed__0();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_empty___closed__0);
l_Lean_Parser_SyntaxStack_empty___closed__1 = _init_l_Lean_Parser_SyntaxStack_empty___closed__1();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_empty___closed__1);
l_Lean_Parser_SyntaxStack_empty = _init_l_Lean_Parser_SyntaxStack_empty();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_empty);
l_Lean_Parser_SyntaxStack_back___closed__0 = _init_l_Lean_Parser_SyntaxStack_back___closed__0();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__0);
l_Lean_Parser_SyntaxStack_back___closed__1 = _init_l_Lean_Parser_SyntaxStack_back___closed__1();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__1);
l_Lean_Parser_SyntaxStack_back___closed__2 = _init_l_Lean_Parser_SyntaxStack_back___closed__2();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__2);
l_Lean_Parser_SyntaxStack_back___closed__3 = _init_l_Lean_Parser_SyntaxStack_back___closed__3();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_back___closed__3);
l_Lean_Parser_SyntaxStack_get_x21___closed__0 = _init_l_Lean_Parser_SyntaxStack_get_x21___closed__0();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_get_x21___closed__0);
l_Lean_Parser_SyntaxStack_get_x21___closed__1 = _init_l_Lean_Parser_SyntaxStack_get_x21___closed__1();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_get_x21___closed__1);
l_Lean_Parser_SyntaxStack_get_x21___closed__2 = _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_get_x21___closed__2);
l_Lean_Parser_SyntaxStack_instHAppendArraySyntax = _init_l_Lean_Parser_SyntaxStack_instHAppendArraySyntax();
lean_mark_persistent(l_Lean_Parser_SyntaxStack_instHAppendArraySyntax);
l_Lean_Parser_ParserState_allErrors___closed__0 = _init_l_Lean_Parser_ParserState_allErrors___closed__0();
lean_mark_persistent(l_Lean_Parser_ParserState_allErrors___closed__0);
l_Lean_Parser_ParserState_allErrors___closed__1 = _init_l_Lean_Parser_ParserState_allErrors___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_allErrors___closed__1);
l_Lean_Parser_ParserState_mkEOIError___closed__0 = _init_l_Lean_Parser_ParserState_mkEOIError___closed__0();
lean_mark_persistent(l_Lean_Parser_ParserState_mkEOIError___closed__0);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2);
l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3 = _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3();
lean_mark_persistent(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0);
l_Lean_Parser_instInhabitedParserFn = _init_l_Lean_Parser_instInhabitedParserFn();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserFn);
l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
l_Lean_Parser_FirstTokens_toStr___closed__0 = _init_l_Lean_Parser_FirstTokens_toStr___closed__0();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__0);
l_Lean_Parser_FirstTokens_toStr___closed__1 = _init_l_Lean_Parser_FirstTokens_toStr___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__1);
l_Lean_Parser_FirstTokens_toStr___closed__2 = _init_l_Lean_Parser_FirstTokens_toStr___closed__2();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__2);
l_Lean_Parser_FirstTokens_instToString___closed__0 = _init_l_Lean_Parser_FirstTokens_instToString___closed__0();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToString___closed__0);
l_Lean_Parser_FirstTokens_instToString = _init_l_Lean_Parser_FirstTokens_instToString();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToString);
l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__0 = _init_l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__0();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__0);
l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__1 = _init_l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lam__1___closed__1);
l_Lean_Parser_instInhabitedParserInfo = _init_l_Lean_Parser_instInhabitedParserInfo();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo);
l_Lean_Parser_instInhabitedParser___closed__0 = _init_l_Lean_Parser_instInhabitedParser___closed__0();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__0);
l_Lean_Parser_instInhabitedParser___closed__1 = _init_l_Lean_Parser_instInhabitedParser___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__1);
l_Lean_Parser_instInhabitedParser___closed__2 = _init_l_Lean_Parser_instInhabitedParser___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__2);
l_Lean_Parser_instInhabitedParser___closed__3 = _init_l_Lean_Parser_instInhabitedParser___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__3);
l_Lean_Parser_instInhabitedParser___closed__4 = _init_l_Lean_Parser_instInhabitedParser___closed__4();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__4);
l_Lean_Parser_instInhabitedParser = _init_l_Lean_Parser_instInhabitedParser();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser);
l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0 = _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0();
lean_mark_persistent(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0);
l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1 = _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1();
lean_mark_persistent(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1);
l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2 = _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2();
lean_mark_persistent(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2);
l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__3 = _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__3();
lean_mark_persistent(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__3);
l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__4 = _init_l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__4();
lean_mark_persistent(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__4);
if (builtin) {res = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ParserFn_run___closed__0 = _init_l_Lean_Parser_ParserFn_run___closed__0();
lean_mark_persistent(l_Lean_Parser_ParserFn_run___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
