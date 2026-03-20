// Lean compiler output
// Module: Lean.Parser.Basic
// Imports: public import Lean.Parser.Types
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCacheFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquots(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
lean_object* l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  pos: "};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__0 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__0_value;
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  err: "};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__1 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__1_value;
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  out: "};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__2 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__2_value;
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__3 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__3_value;
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__4 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__4_value;
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__5 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__5_value;
static const lean_string_object l_Lean_Parser_dbgTraceStateFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_dbgTraceStateFn___closed__6 = (const lean_object*)&l_Lean_Parser_dbgTraceStateFn___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_epsilonInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_epsilonInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_epsilonInfo___closed__0 = (const lean_object*)&l_Lean_Parser_epsilonInfo___closed__0_value;
static const lean_closure_object l_Lean_Parser_epsilonInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_epsilonInfo___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_epsilonInfo___closed__1 = (const lean_object*)&l_Lean_Parser_epsilonInfo___closed__1_value;
static const lean_ctor_object l_Lean_Parser_epsilonInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_epsilonInfo___closed__0_value),((lean_object*)&l_Lean_Parser_epsilonInfo___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_epsilonInfo___closed__2 = (const lean_object*)&l_Lean_Parser_epsilonInfo___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_epsilonInfo = (const lean_object*)&l_Lean_Parser_epsilonInfo___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParserFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instAndThenParserFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instAndThenParserFn___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instAndThenParserFn___closed__0 = (const lean_object*)&l_Lean_Parser_instAndThenParserFn___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instAndThenParserFn = (const lean_object*)&l_Lean_Parser_instAndThenParserFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instAndThenParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instAndThenParser___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instAndThenParser___closed__0 = (const lean_object*)&l_Lean_Parser_instAndThenParser___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instAndThenParser = (const lean_object*)&l_Lean_Parser_instAndThenParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_errorAtSavedPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_epsilonInfo___closed__0_value),((lean_object*)&l_Lean_Parser_epsilonInfo___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_errorAtSavedPos___closed__0 = (const lean_object*)&l_Lean_Parser_errorAtSavedPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "errorAtSavedPos"};
static const lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 209, 12, 134, 87, 184, 144, 74)}};
static const lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3 = (const lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value;
static const lean_string_object l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "Generate an error at the position saved with the `withPosition` combinator.\nIf `delta == true`, then it reports at saved position+1.\nThis useful to make sure a parser consumed at least one character.  "};
static const lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4 = (const lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_checkPrecFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "unexpected token at this precedence level; consider parenthesizing the term"};
static const lean_object* l_Lean_Parser_checkPrecFn___closed__0 = (const lean_object*)&l_Lean_Parser_checkPrecFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_incQuotDepth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_incQuotDepth___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object*);
static lean_once_cell_t l_Lean_Parser_decQuotDepth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_decQuotDepth___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_suppressInsideQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_suppressInsideQuot___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_suppressInsideQuot___closed__0 = (const lean_object*)&l_Lean_Parser_suppressInsideQuot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior = (const lean_object*)&l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__0_value;
static const lean_string_object l_Lean_Parser_orelseFnCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Parser_orelseFnCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_orelseFnCore___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Parser_orelseFnCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_orelseFnCore___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Parser_orelseFnCore___lam__0___closed__1 = (const lean_object*)&l_Lean_Parser_orelseFnCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instOrElseParserFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instOrElseParserFn___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instOrElseParserFn___closed__0 = (const lean_object*)&l_Lean_Parser_instOrElseParserFn___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instOrElseParserFn = (const lean_object*)&l_Lean_Parser_instOrElseParserFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 70, 47, 117, 238, 126, 239, 49)}};
static const lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 322, .m_capacity = 322, .m_length = 321, .m_data = "Run `p`, falling back to `q` if `p` failed without consuming any input.\n\nNOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser\nproducing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`\nis fine as well. "};
static const lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instOrElseParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instOrElseParser___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instOrElseParser___closed__0 = (const lean_object*)&l_Lean_Parser_instOrElseParser___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instOrElseParser = (const lean_object*)&l_Lean_Parser_instOrElseParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object*);
static const lean_string_object l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 16, 254, 130, 153, 255, 99, 153)}};
static const lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 459, .m_capacity = 459, .m_length = 458, .m_data = "The `atomic(p)` parser parses `p`, returns the same result as `p` and fails iff `p` fails,\nbut if `p` fails after consuming some tokens `atomic(p)` will fail without consuming tokens.\nThis is important for the `p <|> q` combinator, because it is not backtracking, and will fail if\n`p` fails after consuming some tokens. To get backtracking behavior, use `atomic(p) <|> q` instead.\n\nThis parser has the same arity as `p` - it produces the same result as `p`. "};
static const lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqRecoveryContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqRecoveryContext_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqRecoveryContext___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqRecoveryContext___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqRecoveryContext = (const lean_object*)&l_Lean_Parser_instBEqRecoveryContext___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialPos"};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7;
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ byteIdx := "};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialSize"};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17;
static lean_once_cell_t l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18;
static const lean_ctor_object l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instReprRecoveryContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instReprRecoveryContext_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instReprRecoveryContext___closed__0 = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instReprRecoveryContext = (const lean_object*)&l_Lean_Parser_instReprRecoveryContext___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "recover'"};
static const lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 86, 208, 93, 10, 1, 153, 43)}};
static const lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 455, .m_capacity = 455, .m_length = 454, .m_data = "Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is provided with information about the failing parser's effects , and it is run in the\nstate immediately after the failure.\n\nThe interactions between <|> and `recover'` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. "};
static const lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 137, 49, 69, 62, 133, 213, 34)}};
static const lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 381, .m_capacity = 381, .m_length = 380, .m_data = "Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is run in the state immediately after the failure.\n\nThe interactions between <|> and `recover` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. "};
static const lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_optionalFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_optionalFn___closed__0 = (const lean_object*)&l_Lean_Parser_optionalFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_optionalFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_optionalFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_optionalFn___closed__1 = (const lean_object*)&l_Lean_Parser_optionalFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object*);
static const lean_string_object l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lookahead"};
static const lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 19, 60, 201, 90, 143, 111, 211)}};
static const lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 310, .m_capacity = 310, .m_length = 309, .m_data = "`lookahead(p)` runs `p` and fails if `p` does, but it produces no parse nodes and rewinds the\nposition to the original state on success. So for example `lookahead(\"=>\")` will ensure that the\nnext token is `\"=>\"`, without actually consuming this token.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_notFollowedByFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unexpected "};
static const lean_object* l_Lean_Parser_notFollowedByFn___closed__0 = (const lean_object*)&l_Lean_Parser_notFollowedByFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "notFollowedBy"};
static const lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 0, 133, 48, 146, 73, 208, 113)}};
static const lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 175, .m_capacity = 175, .m_length = 174, .m_data = "`notFollowedBy(p, \"foo\")` succeeds iff `p` fails;\nif `p` succeeds then it fails with the message `\"unexpected foo\"`.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_manyAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "invalid 'many' parser combinator application, parser did not consume anything"};
static const lean_object* l_Lean_Parser_manyAux___closed__0 = (const lean_object*)&l_Lean_Parser_manyAux___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_many1Unbox___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1Unbox___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_many1Unbox___closed__0 = (const lean_object*)&l_Lean_Parser_many1Unbox___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unterminated comment"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_whitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_whitespace___closed__0 = (const lean_object*)&l_Lean_Parser_whitespace___closed__0_value;
static const lean_closure_object l_Lean_Parser_whitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_takeUntilFn___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_whitespace___closed__0_value)} };
static const lean_object* l_Lean_Parser_whitespace___closed__1 = (const lean_object*)&l_Lean_Parser_whitespace___closed__1_value;
static const lean_string_object l_Lean_Parser_whitespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "isolated carriage returns are not allowed"};
static const lean_object* l_Lean_Parser_whitespace___closed__2 = (const lean_object*)&l_Lean_Parser_whitespace___closed__2_value;
static const lean_string_object l_Lean_Parser_whitespace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "tabs are not allowed; please configure your editor to expand them"};
static const lean_object* l_Lean_Parser_whitespace___closed__3 = (const lean_object*)&l_Lean_Parser_whitespace___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_chFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Parser_chFn___closed__0 = (const lean_object*)&l_Lean_Parser_chFn___closed__0_value;
static const lean_string_object l_Lean_Parser_chFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_chFn___closed__1 = (const lean_object*)&l_Lean_Parser_chFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_hexDigitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "invalid hexadecimal numeral"};
static const lean_object* l_Lean_Parser_hexDigitFn___closed__0 = (const lean_object*)&l_Lean_Parser_hexDigitFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_stringGapFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "expecting newline in string gap"};
static const lean_object* l_Lean_Parser_stringGapFn___closed__0 = (const lean_object*)&l_Lean_Parser_stringGapFn___closed__0_value;
static const lean_string_object l_Lean_Parser_stringGapFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "unexpected additional newline in string gap"};
static const lean_object* l_Lean_Parser_stringGapFn___closed__1 = (const lean_object*)&l_Lean_Parser_stringGapFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_quotedCharCoreFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid escape sequence"};
static const lean_object* l_Lean_Parser_quotedCharCoreFn___closed__0 = (const lean_object*)&l_Lean_Parser_quotedCharCoreFn___closed__0_value;
static lean_once_cell_t l_Lean_Parser_quotedCharCoreFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__1;
static lean_once_cell_t l_Lean_Parser_quotedCharCoreFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_quotedCharFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_isQuotableCharDefault___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_quotedCharFn___closed__0 = (const lean_object*)&l_Lean_Parser_quotedCharFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_charLitFnAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "missing end of character literal"};
static const lean_object* l_Lean_Parser_charLitFnAux___closed__0 = (const lean_object*)&l_Lean_Parser_charLitFnAux___closed__0_value;
static const lean_string_object l_Lean_Parser_charLitFnAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Parser_charLitFnAux___closed__1 = (const lean_object*)&l_Lean_Parser_charLitFnAux___closed__1_value;
static const lean_ctor_object l_Lean_Parser_charLitFnAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_charLitFnAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Parser_charLitFnAux___closed__2 = (const lean_object*)&l_Lean_Parser_charLitFnAux___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_strLitFnAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Parser_strLitFnAux___closed__0 = (const lean_object*)&l_Lean_Parser_strLitFnAux___closed__0_value;
static const lean_ctor_object l_Lean_Parser_strLitFnAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_strLitFnAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Parser_strLitFnAux___closed__1 = (const lean_object*)&l_Lean_Parser_strLitFnAux___closed__1_value;
static const lean_string_object l_Lean_Parser_strLitFnAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unterminated string literal"};
static const lean_object* l_Lean_Parser_strLitFnAux___closed__2 = (const lean_object*)&l_Lean_Parser_strLitFnAux___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "unterminated raw string literal"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_takeDigitsFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected character"};
static const lean_object* l_Lean_Parser_takeDigitsFn___closed__0 = (const lean_object*)&l_Lean_Parser_takeDigitsFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "missing exponent digits in scientific literal"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "decimal number"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "unexpected identifier after decimal point; consider parenthesizing the number"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_decimalNumberFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_decimalNumberFn___closed__0 = (const lean_object*)&l_Lean_Parser_decimalNumberFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_decimalNumberFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_decimalNumberFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_decimalNumberFn___closed__1 = (const lean_object*)&l_Lean_Parser_decimalNumberFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_binNumberFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_binNumberFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_binNumberFn___closed__0 = (const lean_object*)&l_Lean_Parser_binNumberFn___closed__0_value;
static const lean_string_object l_Lean_Parser_binNumberFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binary number"};
static const lean_object* l_Lean_Parser_binNumberFn___closed__1 = (const lean_object*)&l_Lean_Parser_binNumberFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_octalNumberFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_octalNumberFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_octalNumberFn___closed__0 = (const lean_object*)&l_Lean_Parser_octalNumberFn___closed__0_value;
static const lean_string_object l_Lean_Parser_octalNumberFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "octal number"};
static const lean_object* l_Lean_Parser_octalNumberFn___closed__1 = (const lean_object*)&l_Lean_Parser_octalNumberFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_hexNumberFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_hexNumberFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_hexNumberFn___closed__0 = (const lean_object*)&l_Lean_Parser_hexNumberFn___closed__0_value;
static const lean_string_object l_Lean_Parser_hexNumberFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "hexadecimal number"};
static const lean_object* l_Lean_Parser_hexNumberFn___closed__1 = (const lean_object*)&l_Lean_Parser_hexNumberFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_numberFnAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numeral"};
static const lean_object* l_Lean_Parser_numberFnAux___closed__0 = (const lean_object*)&l_Lean_Parser_numberFnAux___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkTokenAndFixPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__0 = (const lean_object*)&l_Lean_Parser_mkTokenAndFixPos___closed__0_value;
static const lean_string_object l_Lean_Parser_mkTokenAndFixPos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forbidden token"};
static const lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__1 = (const lean_object*)&l_Lean_Parser_mkTokenAndFixPos___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0_value;
static const lean_closure_object l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unterminated identifier escape"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid Name literal"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_nonReservedSymbolInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__0 = (const lean_object*)&l_Lean_Parser_nonReservedSymbolInfo___closed__0_value;
static const lean_ctor_object l_Lean_Parser_nonReservedSymbolInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_nonReservedSymbolInfo___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__1 = (const lean_object*)&l_Lean_Parser_nonReservedSymbolInfo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
static const lean_string_object l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "checkWsBefore"};
static const lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 180, 243, 53, 77, 82, 55, 205)}};
static const lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 216, .m_capacity = 216, .m_length = 215, .m_data = "The `ws` parser requires that there is some whitespace at this location.\nFor example, the parser `\"foo\" ws \"+\"` parses `foo +` or `foo/- -/+` but not `foo+`.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_checkTailLinebreak___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Parser_checkTailLinebreak___closed__0 = (const lean_object*)&l_Lean_Parser_checkTailLinebreak___closed__0_value;
static const lean_string_object l_Lean_Parser_checkTailLinebreak___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Parser_checkTailLinebreak___closed__1 = (const lean_object*)&l_Lean_Parser_checkTailLinebreak___closed__1_value;
static const lean_string_object l_Lean_Parser_checkTailLinebreak___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Parser_checkTailLinebreak___closed__2 = (const lean_object*)&l_Lean_Parser_checkTailLinebreak___closed__2_value;
static lean_once_cell_t l_Lean_Parser_checkTailLinebreak___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_checkTailLinebreak___closed__3;
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
static const lean_string_object l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "checkLinebreakBefore"};
static const lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 136, 117, 184, 203, 101, 193, 45)}};
static const lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 188, .m_capacity = 188, .m_length = 187, .m_data = "The `linebreak` parser requires that there is at least one line break at this location.\n(The line break may be inside a comment.)\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
static const lean_string_object l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkNoWsBefore"};
static const lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 175, 148, 38, 136, 238, 167, 124)}};
static const lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 413, .m_capacity = 413, .m_length = 412, .m_data = "The `noWs` parser requires that there is *no* whitespace between the preceding and following\nparsers. For example, the parser `\"foo\" noWs \"+\"` parses `foo+` but not `foo +`.\n\nThis is almost the same as `\"foo+\"`, but using this parser will make `foo+` a token, which may cause\nproblems for the use of `\"foo\"` and `\"+\"` as separate tokens in other parsers.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_unicodeSymbolFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "', '"};
static const lean_object* l_Lean_Parser_unicodeSymbolFn___closed__0 = (const lean_object*)&l_Lean_Parser_unicodeSymbolFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_numLitNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_numLitNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_numLitNoAntiquot;
static const lean_string_object l_Lean_Parser_hexnumFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l_Lean_Parser_hexnumFn___closed__0 = (const lean_object*)&l_Lean_Parser_hexnumFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_hexnumFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_hexnumFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l_Lean_Parser_hexnumFn___closed__1 = (const lean_object*)&l_Lean_Parser_hexnumFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_hexnumNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hexnumNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_hexnumNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hexnumNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumNoAntiquot;
static const lean_string_object l_Lean_Parser_scientificLitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "scientific number"};
static const lean_object* l_Lean_Parser_scientificLitFn___closed__0 = (const lean_object*)&l_Lean_Parser_scientificLitFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_scientificLitNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_scientificLitNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitNoAntiquot;
static const lean_string_object l_Lean_Parser_strLitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "string literal"};
static const lean_object* l_Lean_Parser_strLitFn___closed__0 = (const lean_object*)&l_Lean_Parser_strLitFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_strLitNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_strLitNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_strLitNoAntiquot;
static const lean_string_object l_Lean_Parser_charLitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "character literal"};
static const lean_object* l_Lean_Parser_charLitFn___closed__0 = (const lean_object*)&l_Lean_Parser_charLitFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_charLitNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_charLitNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_charLitNoAntiquot;
static const lean_string_object l_Lean_Parser_nameLitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Parser_nameLitFn___closed__0 = (const lean_object*)&l_Lean_Parser_nameLitFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_nameLitFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_nameLitFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Parser_nameLitFn___closed__1 = (const lean_object*)&l_Lean_Parser_nameLitFn___closed__1_value;
static const lean_string_object l_Lean_Parser_nameLitFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Name literal"};
static const lean_object* l_Lean_Parser_nameLitFn___closed__2 = (const lean_object*)&l_Lean_Parser_nameLitFn___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_nameLitNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_nameLitNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitNoAntiquot;
static const lean_ctor_object l_Lean_Parser_identFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_nonReservedSymbolInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_identFn___closed__0 = (const lean_object*)&l_Lean_Parser_identFn___closed__0_value;
static const lean_string_object l_Lean_Parser_identFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identifier"};
static const lean_object* l_Lean_Parser_identFn___closed__1 = (const lean_object*)&l_Lean_Parser_identFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_identNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_identNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_identNoAntiquot;
static const lean_closure_object l_Lean_Parser_rawIdentNoAntiquot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdentFn___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__0 = (const lean_object*)&l_Lean_Parser_rawIdentNoAntiquot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_rawIdentNoAntiquot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_errorAtSavedPos___closed__0_value),((lean_object*)&l_Lean_Parser_rawIdentNoAntiquot___closed__0_value)}};
static const lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__1 = (const lean_object*)&l_Lean_Parser_rawIdentNoAntiquot___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_rawIdentNoAntiquot = (const lean_object*)&l_Lean_Parser_rawIdentNoAntiquot___closed__1_value;
static const lean_ctor_object l_Lean_Parser_identEqFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_identFn___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_identEqFn___closed__0 = (const lean_object*)&l_Lean_Parser_identEqFn___closed__0_value;
static const lean_string_object l_Lean_Parser_identEqFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "identifier '"};
static const lean_object* l_Lean_Parser_identEqFn___closed__1 = (const lean_object*)&l_Lean_Parser_identEqFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object*);
static const lean_string_object l_Lean_Parser_hygieneInfoFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_hygieneInfoFn___closed__0 = (const lean_object*)&l_Lean_Parser_hygieneInfoFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_hygieneInfoFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_hygieneInfoFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_hygieneInfoFn___closed__1 = (const lean_object*)&l_Lean_Parser_hygieneInfoFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hygieneInfoNoAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hygieneInfoNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_invalidLongestMatchParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "longestMatch parsers must generate exactly one Syntax node"};
static const lean_object* l_Lean_Parser_invalidLongestMatchParser___closed__0 = (const lean_object*)&l_Lean_Parser_invalidLongestMatchParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_longestMatchFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "longestMatch: empty list"};
static const lean_object* l_Lean_Parser_longestMatchFn___closed__0 = (const lean_object*)&l_Lean_Parser_longestMatchFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_anyOfFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "anyOf: empty list"};
static const lean_object* l_Lean_Parser_anyOfFn___closed__0 = (const lean_object*)&l_Lean_Parser_anyOfFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object*);
static const lean_string_object l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColEq"};
static const lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 79, 136, 97, 27, 86, 56, 4)}};
static const lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 299, .m_capacity = 299, .m_length = 298, .m_data = "The `colEq` parser ensures that the next token starts at exactly the column of the saved\nposition (see `withPosition`). This can be used to do whitespace sensitive syntax like\na `by` block or `do` block, where all the lines have to line up.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object*);
static const lean_string_object l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGe"};
static const lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 21, 222, 233, 68, 88, 239, 150)}};
static const lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 474, .m_capacity = 474, .m_length = 473, .m_data = "The `colGe` parser requires that the next token starts from at least the column of the saved\nposition (see `withPosition`), but allows it to be more indented.\nThis can be used for whitespace sensitive syntax to ensure that a block does not go outside a\ncertain indentation scope. For example it is used in the lean grammar for `else if`, to ensure\nthat the `else` is not less indented than the `if` it matches with.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object*);
static const lean_string_object l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGt"};
static const lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 27, 6, 116, 51, 223, 220, 245)}};
static const lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 572, .m_capacity = 572, .m_length = 571, .m_data = "The `colGt` parser requires that the next token starts a strictly greater column than the saved\nposition (see `withPosition`). This can be used for whitespace sensitive syntax for the arguments\nto a tactic, to ensure that the following tactic is not interpreted as an argument.\n```\nexample (x : False) : False := by\n  revert x\n  exact id\n```\nHere, the `revert` tactic is followed by a list of `colGt ident`, because otherwise it would\ninterpret `exact` as an identifier and try to revert a variable named `exact`.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object*);
static const lean_string_object l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checkLineEq"};
static const lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 130, 255, 142, 22, 38, 200, 197)}};
static const lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 367, .m_capacity = 367, .m_length = 366, .m_data = "The `lineEq` parser requires that the current token is on the same line as the saved position\n(see `withPosition`). This can be used to ensure that composite tokens are not \"broken up\" across\ndifferent lines. For example, `else if` is parsed using `lineEq` to ensure that the two tokens\nare on the same line.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object*);
static const lean_string_object l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 188, 255, 221, 143, 31, 128, 82)}};
static const lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 761, .m_capacity = 761, .m_length = 760, .m_data = "`withPosition(p)` runs `p` while setting the \"saved position\" to the current position.\nThis has no effect on its own, but various other parsers access this position to achieve some\ncomposite effect:\n\n* `colGt`, `colGe`, `colEq` compare the column of the saved position to the current position,\n  used to implement Python-style indentation sensitive blocks\n* `lineEq` ensures that the current position is still on the same line as the saved position,\n  used to implement composite tokens\n\nThe saved position is only available in the read-only state, which is why this is a scoping parser:\nafter the `withPosition(..)` block the saved position will be restored to its original value.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_withoutPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_withoutPosition___closed__0 = (const lean_object*)&l_Lean_Parser_withoutPosition___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object*);
static const lean_string_object l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 222, 221, 61, 47, 46, 252, 242)}};
static const lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 331, .m_capacity = 331, .m_length = 330, .m_data = "`withoutPosition(p)` runs `p` without the saved position, meaning that position-checking\nparsers like `colGt` will have no effect. This is usually used by bracketing constructs like\n`(...)` so that the user can locally override whitespace sensitivity.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withForbidden"};
static const lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 169, 160, 142, 191, 14, 119, 146)}};
static const lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 497, .m_capacity = 497, .m_length = 496, .m_data = "`withForbidden tk p` runs `p` with `tk` as a \"forbidden token\". This means that if the token\nappears anywhere in `p` (unless it is nested in `withoutForbidden`), parsing will immediately\nstop there, making `tk` effectively a lowest-precedence operator. This is used for parsers like\n`for x in arr do ...`: `arr` is parsed as `withForbidden \"do\" term` because otherwise `arr do ...`\nwould be treated as an application.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_withoutForbidden___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_withoutForbidden___closed__0 = (const lean_object*)&l_Lean_Parser_withoutForbidden___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
static const lean_string_object l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withoutForbidden"};
static const lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 219, 174, 6, 42, 106, 219)}};
static const lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 302, .m_capacity = 302, .m_length = 301, .m_data = "`withoutForbidden(p)` runs `p` disabling the \"forbidden token\" (see `withForbidden`), if any.\nThis is usually used by bracketing constructs like `(...)` because there is no parsing ambiguity\ninside these nested constructs.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_eoiFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected end of file"};
static const lean_object* l_Lean_Parser_eoiFn___closed__0 = (const lean_object*)&l_Lean_Parser_eoiFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_eoi___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_eoi___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_eoi;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_instInhabitedPrattParsingTables___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_instInhabitedPrattParsingTables___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedPrattParsingTables___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedPrattParsingTables = (const lean_object*)&l_Lean_Parser_instInhabitedPrattParsingTables___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instInhabitedLeadingIdentBehavior_default;
LEAN_EXPORT uint8_t l_Lean_Parser_instInhabitedLeadingIdentBehavior;
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqLeadingIdentBehavior___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqLeadingIdentBehavior___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior = (const lean_object*)&l_Lean_Parser_instBEqLeadingIdentBehavior___closed__0_value;
static const lean_string_object l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Parser.LeadingIdentBehavior.default"};
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__0 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__0_value)}};
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1_value;
static const lean_string_object l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Parser.LeadingIdentBehavior.symbol"};
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__2 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__2_value)}};
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3_value;
static const lean_string_object l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Parser.LeadingIdentBehavior.both"};
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__4 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__4_value;
static const lean_ctor_object l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__4_value)}};
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5_value;
static lean_once_cell_t l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instReprLeadingIdentBehavior___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior___closed__0 = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instReprLeadingIdentBehavior = (const lean_object*)&l_Lean_Parser_instReprLeadingIdentBehavior___closed__0_value;
static lean_once_cell_t l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedParserCategory_default___closed__0;
static lean_once_cell_t l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedParserCategory_default___closed__1;
static lean_once_cell_t l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedParserCategory_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserCategory_default;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserCategory;
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnRef;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_categoryParserFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_categoryParserFn___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_categoryParserFn___closed__0 = (const lean_object*)&l_Lean_Parser_categoryParserFn___closed__0_value;
static const lean_closure_object l_Lean_Parser_categoryParserFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Pi_instInhabited___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_categoryParserFn___closed__0_value)} };
static const lean_object* l_Lean_Parser_categoryParserFn___closed__1 = (const lean_object*)&l_Lean_Parser_categoryParserFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_termParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_termParser___closed__0 = (const lean_object*)&l_Lean_Parser_termParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_termParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_termParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_termParser___closed__1 = (const lean_object*)&l_Lean_Parser_termParser___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object*);
static const lean_string_object l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "unexpected ':'"};
static const lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_checkNoImmediateColon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_checkNoImmediateColon___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_checkNoImmediateColon___closed__0 = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkNoImmediateColon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_errorAtSavedPos___closed__0_value),((lean_object*)&l_Lean_Parser_checkNoImmediateColon___closed__0_value)}};
static const lean_object* l_Lean_Parser_checkNoImmediateColon___closed__1 = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_checkNoImmediateColon = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___closed__1_value;
static const lean_string_object l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "checkNoImmediateColon"};
static const lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 36, 224, 107, 75, 228, 108, 120)}};
static const lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Fail if previous token is immediately followed by ':'. "};
static const lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_pushNone___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_pushNone___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_pushNone___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Parser_pushNone___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Parser_optionalFn___closed__1_value),((lean_object*)&l_Lean_Parser_pushNone___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Parser_pushNone___lam__0___closed__1 = (const lean_object*)&l_Lean_Parser_pushNone___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_pushNone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_pushNone___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_pushNone___closed__0 = (const lean_object*)&l_Lean_Parser_pushNone___closed__0_value;
static const lean_ctor_object l_Lean_Parser_pushNone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_errorAtSavedPos___closed__0_value),((lean_object*)&l_Lean_Parser_pushNone___closed__0_value)}};
static const lean_object* l_Lean_Parser_pushNone___closed__1 = (const lean_object*)&l_Lean_Parser_pushNone___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_pushNone = (const lean_object*)&l_Lean_Parser_pushNone___closed__1_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "antiquotNestedExpr"};
static const lean_object* l_Lean_Parser_antiquotNestedExpr___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_antiquotNestedExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_antiquotNestedExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 217, 111, 200, 191, 162, 168, 125)}};
static const lean_object* l_Lean_Parser_antiquotNestedExpr___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr___closed__1_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_antiquotNestedExpr___closed__2 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr___closed__2_value;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__3;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__4;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__5;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__6;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__7;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__8;
static lean_once_cell_t l_Lean_Parser_antiquotNestedExpr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr;
static const lean_string_object l_Lean_Parser_antiquotExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_antiquotExpr___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotExpr___closed__0_value;
static lean_once_cell_t l_Lean_Parser_antiquotExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotExpr___closed__1;
static lean_once_cell_t l_Lean_Parser_antiquotExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotExpr___closed__2;
static lean_once_cell_t l_Lean_Parser_antiquotExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr;
static const lean_string_object l_Lean_Parser_tokenAntiquotFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "no space before"};
static const lean_object* l_Lean_Parser_tokenAntiquotFn___closed__0 = (const lean_object*)&l_Lean_Parser_tokenAntiquotFn___closed__0_value;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__1;
static const lean_string_object l_Lean_Parser_tokenAntiquotFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l_Lean_Parser_tokenAntiquotFn___closed__2 = (const lean_object*)&l_Lean_Parser_tokenAntiquotFn___closed__2_value;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__3;
static const lean_string_object l_Lean_Parser_tokenAntiquotFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Parser_tokenAntiquotFn___closed__4 = (const lean_object*)&l_Lean_Parser_tokenAntiquotFn___closed__4_value;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__5;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__6;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__7;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__8;
static lean_once_cell_t l_Lean_Parser_tokenAntiquotFn___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_tokenAntiquotFn___closed__9;
static const lean_string_object l_Lean_Parser_tokenAntiquotFn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "token_antiquot"};
static const lean_object* l_Lean_Parser_tokenAntiquotFn___closed__10 = (const lean_object*)&l_Lean_Parser_tokenAntiquotFn___closed__10_value;
static const lean_ctor_object l_Lean_Parser_tokenAntiquotFn___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_tokenAntiquotFn___closed__10_value),LEAN_SCALAR_PTR_LITERAL(33, 159, 231, 44, 235, 156, 55, 135)}};
static const lean_object* l_Lean_Parser_tokenAntiquotFn___closed__11 = (const lean_object*)&l_Lean_Parser_tokenAntiquotFn___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeStringParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeStringParser___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeStringParser___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeStringParser = (const lean_object*)&l_Lean_Parser_instCoeStringParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__0;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__1;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__2;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__3;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__4;
static const lean_string_object l_Lean_Parser_mkAntiquot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "no space before spliced term"};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__5 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__5_value;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__6;
static const lean_string_object l_Lean_Parser_mkAntiquot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__7 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 12, 45, 178, 67, 53, 106)}};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__8 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__8_value;
static const lean_string_object l_Lean_Parser_mkAntiquot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__9 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__9_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___closed__9_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__10 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__10_value;
static const lean_string_object l_Lean_Parser_mkAntiquot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "no space before ':"};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__11 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__11_value;
static const lean_string_object l_Lean_Parser_mkAntiquot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__12 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__12_value;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__13;
static lean_once_cell_t l_Lean_Parser_mkAntiquot___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot___closed__14;
static const lean_string_object l_Lean_Parser_mkAntiquot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pseudo"};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__15 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__15_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 255, 48, 87, 29, 98, 48, 237)}};
static const lean_object* l_Lean_Parser_mkAntiquot___closed__16 = (const lean_object*)&l_Lean_Parser_mkAntiquot___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkAntiquot"};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 252, 121, 56, 15, 15, 211, 216)}};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 257, .m_capacity = 257, .m_length = 256, .m_data = "Define parser for `$e` (if `anonymous == true`) and `$e:name`.\n`kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.\nAntiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`. "};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withAntiquot"};
static const lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 88, 47, 17, 27, 77, 70, 127)}};
static const lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Optimized version of `mkAntiquot ... <|> p`. "};
static const lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquotSplice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquotSplice___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 75, 125, 66, 98, 92, 21, 108)}};
static const lean_object* l_Lean_Parser_mkAntiquotSplice___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice___closed__1_value;
static lean_once_cell_t l_Lean_Parser_mkAntiquotSplice___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__2;
static lean_once_cell_t l_Lean_Parser_mkAntiquotSplice___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mkAntiquotSplice"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 175, 234, 39, 152, 246, 57, 50)}};
static const lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Parse `$[p]suffix`, e.g. `$[p],*`. "};
static const lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "antiquot_suffix_splice"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 22, 214, 220, 194, 127, 23, 217)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "withAntiquotSuffixSplice"};
static const lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 216, 213, 160, 91, 190, 161, 104)}};
static const lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node. "};
static const lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_sepByElemParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Parser_sepByElemParser___closed__0 = (const lean_object*)&l_Lean_Parser_sepByElemParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_sepByElemParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_sepByElemParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Parser_sepByElemParser___closed__1 = (const lean_object*)&l_Lean_Parser_sepByElemParser___closed__1_value;
static const lean_string_object l_Lean_Parser_sepByElemParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_sepByElemParser___closed__2 = (const lean_object*)&l_Lean_Parser_sepByElemParser___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_fieldIdxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "field index"};
static const lean_object* l_Lean_Parser_fieldIdxFn___closed__0 = (const lean_object*)&l_Lean_Parser_fieldIdxFn___closed__0_value;
static const lean_string_object l_Lean_Parser_fieldIdxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l_Lean_Parser_fieldIdxFn___closed__1 = (const lean_object*)&l_Lean_Parser_fieldIdxFn___closed__1_value;
static const lean_ctor_object l_Lean_Parser_fieldIdxFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_fieldIdxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l_Lean_Parser_fieldIdxFn___closed__2 = (const lean_object*)&l_Lean_Parser_fieldIdxFn___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_fieldIdx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_fieldIdx___closed__0;
static lean_once_cell_t l_Lean_Parser_fieldIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_fieldIdx___closed__1;
static lean_once_cell_t l_Lean_Parser_fieldIdx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_fieldIdx___closed__2;
static lean_once_cell_t l_Lean_Parser_fieldIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_fieldIdx___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdx;
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_skip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_skip___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_skip___closed__0 = (const lean_object*)&l_Lean_Parser_skip___closed__0_value;
static const lean_ctor_object l_Lean_Parser_skip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_epsilonInfo___closed__2_value),((lean_object*)&l_Lean_Parser_skip___closed__0_value)}};
static const lean_object* l_Lean_Parser_skip___closed__1 = (const lean_object*)&l_Lean_Parser_skip___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_skip = (const lean_object*)&l_Lean_Parser_skip___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0(lean_object* v_s_x27_1_, lean_object* v_x_2_){
_start:
{
lean_inc_ref(v_s_x27_1_);
return v_s_x27_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0___boxed(lean_object* v_s_x27_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Parser_dbgTraceStateFn___lam__0(v_s_x27_3_, v_x_4_);
lean_dec_ref(v_s_x27_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
return v_x_7_;
}
else
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_head_9_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_head_9_);
v_tail_10_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_tail_10_);
lean_dec_ref(v_x_8_);
v___x_11_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0___closed__0));
v___x_12_ = lean_string_append(v_x_7_, v___x_11_);
v___x_13_ = lean_box(0);
v___x_14_ = 0;
v___x_15_ = l_Lean_Syntax_formatStx(v_head_9_, v___x_13_, v___x_14_);
v___x_16_ = l_Std_Format_defWidth;
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = l_Std_Format_pretty(v___x_15_, v___x_16_, v___x_17_, v___x_17_);
v___x_19_ = lean_string_append(v___x_12_, v___x_18_);
lean_dec_ref(v___x_18_);
v_x_7_ = v___x_19_;
v_x_8_ = v_tail_10_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0(lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_25_; 
v___x_25_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__0));
return v___x_25_;
}
else
{
lean_object* v_tail_26_; 
v_tail_26_ = lean_ctor_get(v_x_24_, 1);
if (lean_obj_tag(v_tail_26_) == 0)
{
lean_object* v_head_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_head_27_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_head_27_);
lean_dec_ref(v_x_24_);
v___x_28_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_29_ = lean_box(0);
v___x_30_ = 0;
v___x_31_ = l_Lean_Syntax_formatStx(v_head_27_, v___x_29_, v___x_30_);
v___x_32_ = l_Std_Format_defWidth;
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = l_Std_Format_pretty(v___x_31_, v___x_32_, v___x_33_, v___x_33_);
v___x_35_ = lean_string_append(v___x_28_, v___x_34_);
lean_dec_ref(v___x_34_);
v___x_36_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_head_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint32_t v___x_48_; lean_object* v___x_49_; 
lean_inc(v_tail_26_);
v_head_38_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_head_38_);
lean_dec_ref(v_x_24_);
v___x_39_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_40_ = lean_box(0);
v___x_41_ = 0;
v___x_42_ = l_Lean_Syntax_formatStx(v_head_38_, v___x_40_, v___x_41_);
v___x_43_ = l_Std_Format_defWidth;
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = l_Std_Format_pretty(v___x_42_, v___x_43_, v___x_44_, v___x_44_);
v___x_46_ = lean_string_append(v___x_39_, v___x_45_);
lean_dec_ref(v___x_45_);
v___x_47_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0_spec__0(v___x_46_, v_tail_26_);
v___x_48_ = 93;
v___x_49_ = lean_string_push(v___x_47_, v___x_48_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object* v_label_57_, lean_object* v_p_58_, lean_object* v_c_59_, lean_object* v_s_60_){
_start:
{
lean_object* v_stxStack_61_; lean_object* v_s_x27_62_; lean_object* v_stxStack_63_; lean_object* v_pos_64_; lean_object* v_errorMsg_65_; lean_object* v_sz_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___y_75_; 
v_stxStack_61_ = lean_ctor_get(v_s_60_, 0);
lean_inc_ref(v_stxStack_61_);
v_s_x27_62_ = lean_apply_2(v_p_58_, v_c_59_, v_s_60_);
v_stxStack_63_ = lean_ctor_get(v_s_x27_62_, 0);
lean_inc_ref(v_stxStack_63_);
v_pos_64_ = lean_ctor_get(v_s_x27_62_, 2);
lean_inc(v_pos_64_);
v_errorMsg_65_ = lean_ctor_get(v_s_x27_62_, 4);
lean_inc(v_errorMsg_65_);
v_sz_66_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_61_);
lean_dec_ref(v_stxStack_61_);
v___f_67_ = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_67_, 0, v_s_x27_62_);
v___x_68_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__0));
v___x_69_ = lean_string_append(v_label_57_, v___x_68_);
v___x_70_ = l_Nat_reprFast(v_pos_64_);
v___x_71_ = lean_string_append(v___x_69_, v___x_70_);
lean_dec_ref(v___x_70_);
v___x_72_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__1));
v___x_73_ = lean_string_append(v___x_71_, v___x_72_);
if (lean_obj_tag(v_errorMsg_65_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__4));
v___y_75_ = v___x_87_;
goto v___jp_74_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_val_88_ = lean_ctor_get(v_errorMsg_65_, 0);
lean_inc(v_val_88_);
lean_dec_ref(v_errorMsg_65_);
v___x_89_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__5));
v___x_90_ = l_Lean_Parser_Error_toString(v_val_88_);
v___x_91_ = l_addParenHeuristic(v___x_90_);
v___x_92_ = lean_string_append(v___x_89_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
v___y_75_ = v___x_94_;
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_76_ = lean_string_append(v___x_73_, v___y_75_);
lean_dec_ref(v___y_75_);
v___x_77_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__2));
v___x_78_ = lean_string_append(v___x_76_, v___x_77_);
v___x_79_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_63_);
v___x_80_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_63_, v_sz_66_, v___x_79_);
lean_dec(v___x_79_);
lean_dec(v_sz_66_);
lean_dec_ref(v_stxStack_63_);
v___x_81_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__3));
v___x_82_ = lean_array_to_list(v___x_80_);
v___x_83_ = l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0(v___x_82_);
v___x_84_ = lean_string_append(v___x_81_, v___x_83_);
lean_dec_ref(v___x_83_);
v___x_85_ = lean_string_append(v___x_78_, v___x_84_);
lean_dec_ref(v___x_84_);
v___x_86_ = lean_dbg_trace(v___x_85_, v___f_67_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object* v_label_95_, lean_object* v_p_96_){
_start:
{
lean_object* v_info_97_; lean_object* v_fn_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_info_97_ = lean_ctor_get(v_p_96_, 0);
v_fn_98_ = lean_ctor_get(v_p_96_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_p_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_100_ = v_p_96_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_fn_98_);
lean_inc(v_info_97_);
lean_dec(v_p_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn), 4, 2);
lean_closure_set(v___x_102_, 0, v_label_95_);
lean_closure_set(v___x_102_, 1, v_fn_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_info_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0(lean_object* v___y_107_){
_start:
{
lean_inc(v___y_107_);
return v___y_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0___boxed(lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Parser_epsilonInfo___lam__0(v___y_108_);
lean_dec(v___y_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1(lean_object* v___y_110_){
_start:
{
lean_inc_ref(v___y_110_);
return v___y_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1___boxed(lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Parser_epsilonInfo___lam__1(v___y_111_);
lean_dec_ref(v___y_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___redArg(lean_object* v_p_120_, lean_object* v_msg_121_, lean_object* v_s_122_){
_start:
{
lean_object* v_stxStack_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_stxStack_123_ = lean_ctor_get(v_s_122_, 0);
v___x_124_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_123_);
v___x_125_ = lean_apply_1(v_p_120_, v___x_124_);
v___x_126_ = lean_unbox(v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = 1;
v___x_128_ = lean_box(0);
v___x_129_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_122_, v_msg_121_, v___x_128_, v___x_127_);
return v___x_129_;
}
else
{
lean_dec_ref(v_msg_121_);
return v_s_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object* v_p_130_, lean_object* v_msg_131_, lean_object* v_x_132_, lean_object* v_s_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Parser_checkStackTopFn___redArg(v_p_130_, v_msg_131_, v_s_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object* v_p_135_, lean_object* v_msg_136_, lean_object* v_x_137_, lean_object* v_s_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Parser_checkStackTopFn(v_p_135_, v_msg_136_, v_x_137_, v_s_138_);
lean_dec_ref(v_x_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object* v_p_140_, lean_object* v_msg_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_143_ = lean_alloc_closure((void*)(l_Lean_Parser_checkStackTopFn___boxed), 4, 2);
lean_closure_set(v___x_143_, 0, v_p_140_);
lean_closure_set(v___x_143_, 1, v_msg_141_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
if (lean_obj_tag(v_x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 1;
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
lean_dec_ref(v_x_146_);
v___x_148_ = 0;
return v___x_148_;
}
}
else
{
if (lean_obj_tag(v_x_146_) == 0)
{
uint8_t v___x_149_; 
lean_dec_ref(v_x_145_);
v___x_149_ = 0;
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v_val_151_; uint8_t v___x_152_; 
v_val_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_150_);
lean_dec_ref(v_x_145_);
v_val_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v_x_146_);
v___x_152_ = l_Lean_Parser_instBEqError_beq(v_val_150_, v_val_151_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0___boxed(lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_x_153_, v_x_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object* v_p_157_, lean_object* v_q_158_, lean_object* v_c_159_, lean_object* v_s_160_){
_start:
{
lean_object* v_s_161_; lean_object* v_errorMsg_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
lean_inc_ref(v_c_159_);
v_s_161_ = lean_apply_2(v_p_157_, v_c_159_, v_s_160_);
v_errorMsg_162_ = lean_ctor_get(v_s_161_, 4);
lean_inc(v_errorMsg_162_);
v___x_163_ = lean_box(0);
v___x_164_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_c_159_);
lean_dec_ref(v_q_158_);
return v_s_161_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_apply_2(v_q_158_, v_c_159_, v_s_161_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__0(lean_object* v_collectKinds_166_, lean_object* v_collectKinds_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_apply_1(v_collectKinds_166_, v___y_168_);
v___x_170_ = lean_apply_1(v_collectKinds_167_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__1(lean_object* v_collectTokens_171_, lean_object* v_collectTokens_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_apply_1(v_collectTokens_171_, v___y_173_);
v___x_175_ = lean_apply_1(v_collectTokens_172_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object* v_p_176_, lean_object* v_q_177_){
_start:
{
lean_object* v_collectTokens_178_; lean_object* v_collectKinds_179_; lean_object* v_firstTokens_180_; lean_object* v_collectTokens_181_; lean_object* v_collectKinds_182_; lean_object* v_firstTokens_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_193_; 
v_collectTokens_178_ = lean_ctor_get(v_p_176_, 0);
lean_inc_ref(v_collectTokens_178_);
v_collectKinds_179_ = lean_ctor_get(v_p_176_, 1);
lean_inc_ref(v_collectKinds_179_);
v_firstTokens_180_ = lean_ctor_get(v_p_176_, 2);
lean_inc(v_firstTokens_180_);
lean_dec_ref(v_p_176_);
v_collectTokens_181_ = lean_ctor_get(v_q_177_, 0);
v_collectKinds_182_ = lean_ctor_get(v_q_177_, 1);
v_firstTokens_183_ = lean_ctor_get(v_q_177_, 2);
v_isSharedCheck_193_ = !lean_is_exclusive(v_q_177_);
if (v_isSharedCheck_193_ == 0)
{
v___x_185_ = v_q_177_;
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_firstTokens_183_);
lean_inc(v_collectKinds_182_);
lean_inc(v_collectTokens_181_);
lean_dec(v_q_177_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___f_187_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_187_, 0, v_collectKinds_182_);
lean_closure_set(v___f_187_, 1, v_collectKinds_179_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_188_, 0, v_collectTokens_181_);
lean_closure_set(v___f_188_, 1, v_collectTokens_178_);
v___x_189_ = l_Lean_Parser_FirstTokens_seq(v_firstTokens_180_, v_firstTokens_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 2, v___x_189_);
lean_ctor_set(v___x_185_, 1, v___f_187_);
lean_ctor_set(v___x_185_, 0, v___f_188_);
v___x_191_ = v___x_185_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___f_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___f_187_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParserFn___lam__0(lean_object* v_p1_194_, lean_object* v_p2_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_1(v_p2_195_, v___x_198_);
v___x_200_ = l_Lean_Parser_andthenFn(v_p1_194_, v___x_199_, v___y_196_, v___y_197_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object* v_p_203_, lean_object* v_q_204_){
_start:
{
lean_object* v_info_205_; lean_object* v_fn_206_; lean_object* v_info_207_; lean_object* v_fn_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_217_; 
v_info_205_ = lean_ctor_get(v_p_203_, 0);
lean_inc_ref(v_info_205_);
v_fn_206_ = lean_ctor_get(v_p_203_, 1);
lean_inc_ref(v_fn_206_);
lean_dec_ref(v_p_203_);
v_info_207_ = lean_ctor_get(v_q_204_, 0);
v_fn_208_ = lean_ctor_get(v_q_204_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_q_204_);
if (v_isSharedCheck_217_ == 0)
{
v___x_210_ = v_q_204_;
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_fn_208_);
lean_inc(v_info_207_);
lean_dec(v_q_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = l_Lean_Parser_andthenInfo(v_info_205_, v_info_207_);
v___x_213_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_213_, 0, v_fn_206_);
lean_closure_set(v___x_213_, 1, v_fn_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_213_);
lean_ctor_set(v___x_210_, 0, v___x_212_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser___lam__0(lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_box(0);
v___x_221_ = lean_apply_1(v_b_219_, v___x_220_);
v___x_222_ = l_Lean_Parser_andthen(v_a_218_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object* v_n_225_, lean_object* v_p_226_, lean_object* v_c_227_, lean_object* v_s_228_){
_start:
{
lean_object* v_iniSz_229_; lean_object* v_s_230_; lean_object* v___x_231_; 
v_iniSz_229_ = l_Lean_Parser_ParserState_stackSize(v_s_228_);
v_s_230_ = lean_apply_2(v_p_226_, v_c_227_, v_s_228_);
v___x_231_ = l_Lean_Parser_ParserState_mkNode(v_s_230_, v_n_225_, v_iniSz_229_);
lean_dec(v_iniSz_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object* v_n_232_, lean_object* v_p_233_, lean_object* v_c_234_, lean_object* v_s_235_){
_start:
{
lean_object* v_iniSz_236_; lean_object* v_s_237_; lean_object* v___x_238_; 
v_iniSz_236_ = l_Lean_Parser_ParserState_stackSize(v_s_235_);
v_s_237_ = lean_apply_2(v_p_233_, v_c_234_, v_s_235_);
v___x_238_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_237_, v_n_232_, v_iniSz_236_);
lean_dec(v_iniSz_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___lam__0(lean_object* v_collectKinds_239_, lean_object* v_n_240_, lean_object* v_s_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_apply_1(v_collectKinds_239_, v_s_241_);
v___x_243_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v___x_242_, v_n_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object* v_n_244_, lean_object* v_p_245_){
_start:
{
lean_object* v_collectTokens_246_; lean_object* v_collectKinds_247_; lean_object* v_firstTokens_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_collectTokens_246_ = lean_ctor_get(v_p_245_, 0);
v_collectKinds_247_ = lean_ctor_get(v_p_245_, 1);
v_firstTokens_248_ = lean_ctor_get(v_p_245_, 2);
v_isSharedCheck_256_ = !lean_is_exclusive(v_p_245_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v_p_245_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_firstTokens_248_);
lean_inc(v_collectKinds_247_);
lean_inc(v_collectTokens_246_);
lean_dec(v_p_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___f_252_; lean_object* v___x_254_; 
v___f_252_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___lam__0), 3, 2);
lean_closure_set(v___f_252_, 0, v_collectKinds_247_);
lean_closure_set(v___f_252_, 1, v_n_244_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v___f_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_collectTokens_246_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___f_252_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_firstTokens_248_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object* v_n_257_, lean_object* v_p_258_){
_start:
{
lean_object* v_info_259_; lean_object* v_fn_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_269_; 
v_info_259_ = lean_ctor_get(v_p_258_, 0);
v_fn_260_ = lean_ctor_get(v_p_258_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_p_258_);
if (v_isSharedCheck_269_ == 0)
{
v___x_262_ = v_p_258_;
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_fn_260_);
lean_inc(v_info_259_);
lean_dec(v_p_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
lean_inc(v_n_257_);
v___x_264_ = l_Lean_Parser_nodeInfo(v_n_257_, v_info_259_);
v___x_265_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v___x_265_, 0, v_n_257_);
lean_closure_set(v___x_265_, 1, v_fn_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_265_);
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_267_ = v___x_262_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___redArg(lean_object* v_msg_270_, lean_object* v_s_271_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_box(0);
v___x_273_ = 1;
v___x_274_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_271_, v_msg_270_, v___x_272_, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object* v_msg_275_, lean_object* v_x_276_, lean_object* v_s_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Parser_errorFn___redArg(v_msg_275_, v_s_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object* v_msg_279_, lean_object* v_x_280_, lean_object* v_s_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Parser_errorFn(v_msg_279_, v_x_280_, v_s_281_);
lean_dec_ref(v_x_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object* v_msg_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_285_ = lean_alloc_closure((void*)(l_Lean_Parser_errorFn___boxed), 3, 1);
lean_closure_set(v___x_285_, 0, v_msg_283_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* v_msg_287_, uint8_t v_delta_288_, lean_object* v_c_289_, lean_object* v_s_290_){
_start:
{
lean_object* v_toCacheableParserContext_291_; lean_object* v_savedPos_x3f_292_; 
v_toCacheableParserContext_291_ = lean_ctor_get(v_c_289_, 2);
v_savedPos_x3f_292_ = lean_ctor_get(v_toCacheableParserContext_291_, 2);
lean_inc(v_savedPos_x3f_292_);
if (lean_obj_tag(v_savedPos_x3f_292_) == 0)
{
lean_dec_ref(v_c_289_);
lean_dec_ref(v_msg_287_);
return v_s_290_;
}
else
{
if (v_delta_288_ == 0)
{
lean_object* v_val_293_; lean_object* v___x_294_; 
lean_dec_ref(v_c_289_);
v_val_293_ = lean_ctor_get(v_savedPos_x3f_292_, 0);
lean_inc(v_val_293_);
lean_dec_ref(v_savedPos_x3f_292_);
v___x_294_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_290_, v_msg_287_, v_val_293_);
return v___x_294_;
}
else
{
lean_object* v_toInputContext_295_; lean_object* v_val_296_; lean_object* v_inputString_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_toInputContext_295_ = lean_ctor_get(v_c_289_, 0);
lean_inc_ref(v_toInputContext_295_);
lean_dec_ref(v_c_289_);
v_val_296_ = lean_ctor_get(v_savedPos_x3f_292_, 0);
lean_inc(v_val_296_);
lean_dec_ref(v_savedPos_x3f_292_);
v_inputString_297_ = lean_ctor_get(v_toInputContext_295_, 0);
lean_inc_ref(v_inputString_297_);
lean_dec_ref(v_toInputContext_295_);
v___x_298_ = lean_string_utf8_next(v_inputString_297_, v_val_296_);
lean_dec(v_val_296_);
lean_dec_ref(v_inputString_297_);
v___x_299_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_290_, v_msg_287_, v___x_298_);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object* v_msg_300_, lean_object* v_delta_301_, lean_object* v_c_302_, lean_object* v_s_303_){
_start:
{
uint8_t v_delta_boxed_304_; lean_object* v_res_305_; 
v_delta_boxed_304_ = lean_unbox(v_delta_301_);
v_res_305_ = l_Lean_Parser_errorAtSavedPosFn(v_msg_300_, v_delta_boxed_304_, v_c_302_, v_s_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object* v_msg_310_, uint8_t v_delta_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_313_ = lean_box(v_delta_311_);
v___x_314_ = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn___boxed), 4, 2);
lean_closure_set(v___x_314_, 0, v_msg_310_);
lean_closure_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object* v_msg_316_, lean_object* v_delta_317_){
_start:
{
uint8_t v_delta_boxed_318_; lean_object* v_res_319_; 
v_delta_boxed_318_ = lean_unbox(v_delta_317_);
v_res_319_ = l_Lean_Parser_errorAtSavedPos(v_msg_316_, v_delta_boxed_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3));
v___x_330_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4));
v___x_331_ = l_Lean_addBuiltinDocString(v___x_329_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___boxed(lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object* v_prec_335_, lean_object* v_c_336_, lean_object* v_s_337_){
_start:
{
lean_object* v_toCacheableParserContext_338_; lean_object* v_prec_339_; uint8_t v___x_340_; 
v_toCacheableParserContext_338_ = lean_ctor_get(v_c_336_, 2);
v_prec_339_ = lean_ctor_get(v_toCacheableParserContext_338_, 0);
v___x_340_ = lean_nat_dec_le(v_prec_339_, v_prec_335_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_341_ = ((lean_object*)(l_Lean_Parser_checkPrecFn___closed__0));
v___x_342_ = lean_box(0);
v___x_343_ = 1;
v___x_344_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_337_, v___x_341_, v___x_342_, v___x_343_);
return v___x_344_;
}
else
{
return v_s_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object* v_prec_345_, lean_object* v_c_346_, lean_object* v_s_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Parser_checkPrecFn(v_prec_345_, v_c_346_, v_s_347_);
lean_dec_ref(v_c_346_);
lean_dec(v_prec_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object* v_prec_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_351_ = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(v___x_351_, 0, v_prec_349_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg(lean_object* v_prec_353_, lean_object* v_s_354_){
_start:
{
lean_object* v_lhsPrec_355_; uint8_t v___x_356_; 
v_lhsPrec_355_ = lean_ctor_get(v_s_354_, 1);
v___x_356_ = lean_nat_dec_le(v_prec_353_, v_lhsPrec_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_357_ = ((lean_object*)(l_Lean_Parser_checkPrecFn___closed__0));
v___x_358_ = lean_box(0);
v___x_359_ = 1;
v___x_360_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_354_, v___x_357_, v___x_358_, v___x_359_);
return v___x_360_;
}
else
{
return v_s_354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg___boxed(lean_object* v_prec_361_, lean_object* v_s_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Parser_checkLhsPrecFn___redArg(v_prec_361_, v_s_362_);
lean_dec(v_prec_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object* v_prec_364_, lean_object* v_x_365_, lean_object* v_s_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Parser_checkLhsPrecFn___redArg(v_prec_364_, v_s_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object* v_prec_368_, lean_object* v_x_369_, lean_object* v_s_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Parser_checkLhsPrecFn(v_prec_368_, v_x_369_, v_s_370_);
lean_dec_ref(v_x_369_);
lean_dec(v_prec_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object* v_prec_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_374_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(v___x_374_, 0, v_prec_372_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___redArg(lean_object* v_prec_376_, lean_object* v_s_377_){
_start:
{
lean_object* v_stxStack_378_; lean_object* v_pos_379_; lean_object* v_cache_380_; lean_object* v_errorMsg_381_; lean_object* v_recoveredErrors_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_stxStack_378_ = lean_ctor_get(v_s_377_, 0);
v_pos_379_ = lean_ctor_get(v_s_377_, 2);
v_cache_380_ = lean_ctor_get(v_s_377_, 3);
v_errorMsg_381_ = lean_ctor_get(v_s_377_, 4);
v_recoveredErrors_382_ = lean_ctor_get(v_s_377_, 5);
v___x_383_ = lean_box(0);
lean_inc(v_errorMsg_381_);
v___x_384_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_381_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v_prec_376_);
return v_s_377_;
}
else
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_inc_ref(v_recoveredErrors_382_);
lean_inc(v_errorMsg_381_);
lean_inc_ref(v_cache_380_);
lean_inc(v_pos_379_);
lean_inc_ref(v_stxStack_378_);
v_isSharedCheck_391_ = !lean_is_exclusive(v_s_377_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; lean_object* v_unused_393_; lean_object* v_unused_394_; lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_392_ = lean_ctor_get(v_s_377_, 5);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_s_377_, 4);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_s_377_, 3);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_s_377_, 2);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_s_377_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_s_377_, 0);
lean_dec(v_unused_397_);
v___x_386_ = v_s_377_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_s_377_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_prec_376_);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_stxStack_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_prec_376_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_pos_379_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_cache_380_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_errorMsg_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 5, v_recoveredErrors_382_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object* v_prec_398_, lean_object* v_x_399_, lean_object* v_s_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Parser_setLhsPrecFn___redArg(v_prec_398_, v_s_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object* v_prec_402_, lean_object* v_x_403_, lean_object* v_s_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Parser_setLhsPrecFn(v_prec_402_, v_x_403_, v_s_404_);
lean_dec_ref(v_x_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object* v_prec_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_408_ = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(v___x_408_, 0, v_prec_406_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_spec__0(lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_nat_to_int(v_a_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(lean_object* v_i_412_, lean_object* v_c_413_){
_start:
{
lean_object* v_prec_414_; lean_object* v_quotDepth_415_; uint8_t v_suppressInsideQuot_416_; lean_object* v_savedPos_x3f_417_; lean_object* v_forbiddenTk_x3f_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_prec_414_ = lean_ctor_get(v_c_413_, 0);
v_quotDepth_415_ = lean_ctor_get(v_c_413_, 1);
v_suppressInsideQuot_416_ = lean_ctor_get_uint8(v_c_413_, sizeof(void*)*4);
v_savedPos_x3f_417_ = lean_ctor_get(v_c_413_, 2);
v_forbiddenTk_x3f_418_ = lean_ctor_get(v_c_413_, 3);
v_isSharedCheck_428_ = !lean_is_exclusive(v_c_413_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v_c_413_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_forbiddenTk_x3f_418_);
lean_inc(v_savedPos_x3f_417_);
lean_inc(v_quotDepth_415_);
lean_inc(v_prec_414_);
lean_dec(v_c_413_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_422_ = lean_nat_to_int(v_quotDepth_415_);
v___x_423_ = lean_int_add(v___x_422_, v_i_412_);
lean_dec(v___x_422_);
v___x_424_ = l_Int_toNat(v___x_423_);
lean_dec(v___x_423_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_424_);
v___x_426_ = v___x_420_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_prec_414_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_savedPos_x3f_417_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_forbiddenTk_x3f_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*4, v_suppressInsideQuot_416_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed(lean_object* v_i_429_, lean_object* v_c_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(v_i_429_, v_c_430_);
lean_dec(v_i_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object* v_i_432_, lean_object* v_p_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed), 2, 1);
lean_closure_set(v___f_434_, 0, v_i_432_);
v___x_435_ = l_Lean_Parser_adaptCacheableContext(v___f_434_, v_p_433_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Parser_incQuotDepth___closed__0(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_to_int(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object* v_p_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___x_440_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(v___x_439_, v_p_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Parser_decQuotDepth___closed__0(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___x_442_ = lean_int_neg(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object* v_p_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_Parser_decQuotDepth___closed__0, &l_Lean_Parser_decQuotDepth___closed__0_once, _init_l_Lean_Parser_decQuotDepth___closed__0);
v___x_445_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(v___x_444_, v_p_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0(lean_object* v_c_446_){
_start:
{
lean_object* v_prec_447_; lean_object* v_quotDepth_448_; lean_object* v_savedPos_x3f_449_; lean_object* v_forbiddenTk_x3f_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_prec_447_ = lean_ctor_get(v_c_446_, 0);
v_quotDepth_448_ = lean_ctor_get(v_c_446_, 1);
v_savedPos_x3f_449_ = lean_ctor_get(v_c_446_, 2);
v_forbiddenTk_x3f_450_ = lean_ctor_get(v_c_446_, 3);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_eq(v_quotDepth_448_, v___x_451_);
if (v___x_452_ == 0)
{
return v_c_446_;
}
else
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_inc(v_forbiddenTk_x3f_450_);
lean_inc(v_savedPos_x3f_449_);
lean_inc(v_quotDepth_448_);
lean_inc(v_prec_447_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_c_446_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; lean_object* v_unused_461_; lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_460_ = lean_ctor_get(v_c_446_, 3);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_c_446_, 2);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_c_446_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_c_446_, 0);
lean_dec(v_unused_463_);
v___x_454_ = v_c_446_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_dec(v_c_446_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_prec_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_quotDepth_448_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_savedPos_x3f_449_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_forbiddenTk_x3f_450_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*4, v___x_452_);
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* v_a_465_){
_start:
{
lean_object* v___f_466_; lean_object* v___x_467_; 
v___f_466_ = ((lean_object*)(l_Lean_Parser_suppressInsideQuot___closed__0));
v___x_467_ = l_Lean_Parser_adaptCacheableContext(v___f_466_, v_a_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object* v_n_468_, lean_object* v_prec_469_, lean_object* v_p_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_inc(v_prec_469_);
v___x_471_ = l_Lean_Parser_checkPrec(v_prec_469_);
v___x_472_ = l_Lean_Parser_node(v_n_468_, v_p_470_);
v___x_473_ = l_Lean_Parser_setLhsPrec(v_prec_469_);
v___x_474_ = l_Lean_Parser_andthen(v___x_472_, v___x_473_);
v___x_475_ = l_Lean_Parser_andthen(v___x_471_, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object* v_n_476_, lean_object* v_p_477_){
_start:
{
lean_object* v_info_478_; lean_object* v_fn_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_488_; 
v_info_478_ = lean_ctor_get(v_p_477_, 0);
v_fn_479_ = lean_ctor_get(v_p_477_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_p_477_);
if (v_isSharedCheck_488_ == 0)
{
v___x_481_ = v_p_477_;
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_fn_479_);
lean_inc(v_info_478_);
lean_dec(v_p_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_inc(v_n_476_);
v___x_483_ = l_Lean_Parser_nodeInfo(v_n_476_, v_info_478_);
v___x_484_ = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(v___x_484_, 0, v_n_476_);
lean_closure_set(v___x_484_, 1, v_fn_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_484_);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object* v_n_489_, lean_object* v_prec_490_, lean_object* v_lhsPrec_491_, lean_object* v_p_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_inc(v_prec_490_);
v___x_493_ = l_Lean_Parser_checkPrec(v_prec_490_);
v___x_494_ = l_Lean_Parser_checkLhsPrec(v_lhsPrec_491_);
v___x_495_ = l_Lean_Parser_trailingNodeAux(v_n_489_, v_p_492_);
v___x_496_ = l_Lean_Parser_setLhsPrec(v_prec_490_);
v___x_497_ = l_Lean_Parser_andthen(v___x_495_, v___x_496_);
v___x_498_ = l_Lean_Parser_andthen(v___x_494_, v___x_497_);
v___x_499_ = l_Lean_Parser_andthen(v___x_493_, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* v_s_500_, lean_object* v_error1_501_, lean_object* v_iniPos_502_, uint8_t v_mergeErrors_503_){
_start:
{
lean_object* v_stxStack_504_; lean_object* v_lhsPrec_505_; lean_object* v_pos_506_; lean_object* v_cache_507_; lean_object* v_errorMsg_508_; lean_object* v_recoveredErrors_509_; lean_object* v___y_511_; 
v_stxStack_504_ = lean_ctor_get(v_s_500_, 0);
v_lhsPrec_505_ = lean_ctor_get(v_s_500_, 1);
v_pos_506_ = lean_ctor_get(v_s_500_, 2);
v_cache_507_ = lean_ctor_get(v_s_500_, 3);
v_errorMsg_508_ = lean_ctor_get(v_s_500_, 4);
v_recoveredErrors_509_ = lean_ctor_get(v_s_500_, 5);
if (lean_obj_tag(v_errorMsg_508_) == 1)
{
lean_object* v_val_514_; uint8_t v___x_515_; 
v_val_514_ = lean_ctor_get(v_errorMsg_508_, 0);
v___x_515_ = lean_nat_dec_eq(v_pos_506_, v_iniPos_502_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_error1_501_);
return v_s_500_;
}
else
{
lean_inc(v_val_514_);
lean_inc_ref(v_recoveredErrors_509_);
lean_inc_ref(v_cache_507_);
lean_inc(v_pos_506_);
lean_inc(v_lhsPrec_505_);
lean_inc_ref(v_stxStack_504_);
lean_dec_ref(v_s_500_);
if (v_mergeErrors_503_ == 0)
{
lean_dec_ref(v_error1_501_);
v___y_511_ = v_val_514_;
goto v___jp_510_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Parser_Error_merge(v_error1_501_, v_val_514_);
v___y_511_ = v___x_516_;
goto v___jp_510_;
}
}
}
else
{
lean_dec_ref(v_error1_501_);
return v_s_500_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___y_511_);
v___x_513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_513_, 0, v_stxStack_504_);
lean_ctor_set(v___x_513_, 1, v_lhsPrec_505_);
lean_ctor_set(v___x_513_, 2, v_pos_506_);
lean_ctor_set(v___x_513_, 3, v_cache_507_);
lean_ctor_set(v___x_513_, 4, v___x_512_);
lean_ctor_set(v___x_513_, 5, v_recoveredErrors_509_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* v_s_517_, lean_object* v_error1_518_, lean_object* v_iniPos_519_, lean_object* v_mergeErrors_520_){
_start:
{
uint8_t v_mergeErrors_boxed_521_; lean_object* v_res_522_; 
v_mergeErrors_boxed_521_ = lean_unbox(v_mergeErrors_520_);
v_res_522_ = l_Lean_Parser_mergeOrElseErrors(v_s_517_, v_error1_518_, v_iniPos_519_, v_mergeErrors_boxed_521_);
lean_dec(v_iniPos_519_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(uint8_t v_x_523_){
_start:
{
switch(v_x_523_)
{
case 0:
{
lean_object* v___x_524_; 
v___x_524_ = lean_unsigned_to_nat(0u);
return v___x_524_;
}
case 1:
{
lean_object* v___x_525_; 
v___x_525_ = lean_unsigned_to_nat(1u);
return v___x_525_;
}
default: 
{
lean_object* v___x_526_; 
v___x_526_ = lean_unsigned_to_nat(2u);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___boxed(lean_object* v_x_527_){
_start:
{
uint8_t v_x_boxed_528_; lean_object* v_res_529_; 
v_x_boxed_528_ = lean_unbox(v_x_527_);
v_res_529_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_boxed_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object* v_x_532_){
_start:
{
uint8_t v_x_4__boxed_533_; lean_object* v_res_534_; 
v_x_4__boxed_533_ = lean_unbox(v_x_532_);
v_res_534_ = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(v_x_4__boxed_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(lean_object* v_k_535_){
_start:
{
lean_inc(v_k_535_);
return v_k_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg___boxed(lean_object* v_k_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(v_k_536_);
lean_dec(v_k_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_object* v_motive_538_, lean_object* v_ctorIdx_539_, uint8_t v_t_540_, lean_object* v_h_541_, lean_object* v_k_542_){
_start:
{
lean_inc(v_k_542_);
return v_k_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___boxed(lean_object* v_motive_543_, lean_object* v_ctorIdx_544_, lean_object* v_t_545_, lean_object* v_h_546_, lean_object* v_k_547_){
_start:
{
uint8_t v_t_boxed_548_; lean_object* v_res_549_; 
v_t_boxed_548_ = lean_unbox(v_t_545_);
v_res_549_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(v_motive_543_, v_ctorIdx_544_, v_t_boxed_548_, v_h_546_, v_k_547_);
lean_dec(v_k_547_);
lean_dec(v_ctorIdx_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(lean_object* v_acceptLhs_550_){
_start:
{
lean_inc(v_acceptLhs_550_);
return v_acceptLhs_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg___boxed(lean_object* v_acceptLhs_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(v_acceptLhs_551_);
lean_dec(v_acceptLhs_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_object* v_motive_553_, uint8_t v_t_554_, lean_object* v_h_555_, lean_object* v_acceptLhs_556_){
_start:
{
lean_inc(v_acceptLhs_556_);
return v_acceptLhs_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___boxed(lean_object* v_motive_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_acceptLhs_560_){
_start:
{
uint8_t v_t_boxed_561_; lean_object* v_res_562_; 
v_t_boxed_561_ = lean_unbox(v_t_558_);
v_res_562_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(v_motive_557_, v_t_boxed_561_, v_h_559_, v_acceptLhs_560_);
lean_dec(v_acceptLhs_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(lean_object* v_takeLongest_563_){
_start:
{
lean_inc(v_takeLongest_563_);
return v_takeLongest_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg___boxed(lean_object* v_takeLongest_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(v_takeLongest_564_);
lean_dec(v_takeLongest_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_object* v_motive_566_, uint8_t v_t_567_, lean_object* v_h_568_, lean_object* v_takeLongest_569_){
_start:
{
lean_inc(v_takeLongest_569_);
return v_takeLongest_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___boxed(lean_object* v_motive_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_takeLongest_573_){
_start:
{
uint8_t v_t_boxed_574_; lean_object* v_res_575_; 
v_t_boxed_574_ = lean_unbox(v_t_571_);
v_res_575_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(v_motive_570_, v_t_boxed_574_, v_h_572_, v_takeLongest_573_);
lean_dec(v_takeLongest_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(lean_object* v_merge_576_){
_start:
{
lean_inc(v_merge_576_);
return v_merge_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg___boxed(lean_object* v_merge_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(v_merge_577_);
lean_dec(v_merge_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_object* v_motive_579_, uint8_t v_t_580_, lean_object* v_h_581_, lean_object* v_merge_582_){
_start:
{
lean_inc(v_merge_582_);
return v_merge_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___boxed(lean_object* v_motive_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_merge_586_){
_start:
{
uint8_t v_t_boxed_587_; lean_object* v_res_588_; 
v_t_boxed_587_ = lean_unbox(v_t_584_);
v_res_588_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(v_motive_583_, v_t_boxed_587_, v_h_585_, v_merge_586_);
lean_dec(v_merge_586_);
return v_res_588_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(uint8_t v_x_589_, uint8_t v_y_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_589_);
v___x_592_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_y_590_);
v___x_593_ = lean_nat_dec_eq(v___x_591_, v___x_592_);
lean_dec(v___x_592_);
lean_dec(v___x_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed(lean_object* v_x_594_, lean_object* v_y_595_){
_start:
{
uint8_t v_x_17__boxed_596_; uint8_t v_y_18__boxed_597_; uint8_t v_res_598_; lean_object* v_r_599_; 
v_x_17__boxed_596_ = lean_unbox(v_x_594_);
v_y_18__boxed_597_ = lean_unbox(v_y_595_);
v_res_598_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_17__boxed_596_, v_y_18__boxed_597_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object* v_stx_605_, lean_object* v_s_606_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
lean_inc(v_stx_605_);
v___x_608_ = l_Lean_Syntax_isOfKind(v_stx_605_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Parser_ParserState_pushSyntax(v_s_606_, v_stx_605_);
return v___x_609_;
}
else
{
lean_object* v_stxStack_610_; lean_object* v_lhsPrec_611_; lean_object* v_pos_612_; lean_object* v_cache_613_; lean_object* v_errorMsg_614_; lean_object* v_recoveredErrors_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_624_; 
v_stxStack_610_ = lean_ctor_get(v_s_606_, 0);
v_lhsPrec_611_ = lean_ctor_get(v_s_606_, 1);
v_pos_612_ = lean_ctor_get(v_s_606_, 2);
v_cache_613_ = lean_ctor_get(v_s_606_, 3);
v_errorMsg_614_ = lean_ctor_get(v_s_606_, 4);
v_recoveredErrors_615_ = lean_ctor_get(v_s_606_, 5);
v_isSharedCheck_624_ = !lean_is_exclusive(v_s_606_);
if (v_isSharedCheck_624_ == 0)
{
v___x_617_ = v_s_606_;
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_recoveredErrors_615_);
lean_inc(v_errorMsg_614_);
lean_inc(v_cache_613_);
lean_inc(v_pos_612_);
lean_inc(v_lhsPrec_611_);
lean_inc(v_stxStack_610_);
lean_dec(v_s_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = l_Lean_Syntax_getArgs(v_stx_605_);
lean_dec(v_stx_605_);
v___x_620_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stxStack_610_, v___x_619_);
lean_dec_ref(v___x_619_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_lhsPrec_611_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_pos_612_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_cache_613_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_errorMsg_614_);
lean_ctor_set(v_reuseFailAlloc_623_, 5, v_recoveredErrors_615_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* v_p_625_, lean_object* v_q_626_, uint8_t v_antiquotBehavior_627_, lean_object* v_c_628_, lean_object* v_s_629_){
_start:
{
lean_object* v_pos_630_; lean_object* v_iniSz_631_; lean_object* v_s_632_; lean_object* v_errorMsg_633_; 
v_pos_630_ = lean_ctor_get(v_s_629_, 2);
lean_inc(v_pos_630_);
v_iniSz_631_ = l_Lean_Parser_ParserState_stackSize(v_s_629_);
lean_inc_ref(v_c_628_);
v_s_632_ = lean_apply_2(v_p_625_, v_c_628_, v_s_629_);
v_errorMsg_633_ = lean_ctor_get(v_s_632_, 4);
lean_inc(v_errorMsg_633_);
if (lean_obj_tag(v_errorMsg_633_) == 0)
{
lean_object* v_stxStack_634_; lean_object* v_pos_635_; lean_object* v_pBack_636_; lean_object* v___y_638_; lean_object* v___y_642_; uint8_t v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; uint8_t v___y_660_; uint8_t v___x_673_; uint8_t v___x_674_; 
v_stxStack_634_ = lean_ctor_get(v_s_632_, 0);
lean_inc_ref(v_stxStack_634_);
v_pos_635_ = lean_ctor_get(v_s_632_, 2);
lean_inc(v_pos_635_);
v_pBack_636_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_634_);
lean_dec_ref(v_stxStack_634_);
v___x_673_ = 0;
v___x_674_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_627_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_675_ = l_Lean_Parser_ParserState_stackSize(v_s_632_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_iniSz_631_, v___x_676_);
v___x_678_ = lean_nat_dec_eq(v___x_675_, v___x_677_);
lean_dec(v___x_677_);
lean_dec(v___x_675_);
if (v___x_678_ == 0)
{
lean_dec(v_pBack_636_);
lean_dec(v_pos_635_);
lean_dec(v_iniSz_631_);
lean_dec(v_pos_630_);
lean_dec_ref(v_c_628_);
lean_dec_ref(v_q_626_);
return v_s_632_;
}
else
{
v___y_660_ = v___x_674_;
goto v___jp_659_;
}
}
else
{
v___y_660_ = v___x_674_;
goto v___jp_659_;
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = l_Lean_Parser_ParserState_restore(v___y_638_, v_iniSz_631_, v_pos_635_);
lean_dec(v_iniSz_631_);
v___x_640_ = l_Lean_Parser_ParserState_pushSyntax(v___x_639_, v_pBack_636_);
return v___x_640_;
}
v___jp_641_:
{
lean_object* v_stxStack_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_stxStack_643_ = lean_ctor_get(v___y_642_, 0);
v___x_644_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_643_);
lean_inc(v___x_644_);
v___x_645_ = l_Lean_Syntax_isAntiquots(v___x_644_);
if (v___x_645_ == 0)
{
lean_dec(v___x_644_);
v___y_638_ = v___y_642_;
goto v___jp_637_;
}
else
{
lean_object* v_s_646_; lean_object* v_s_647_; lean_object* v_s_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v_pos_635_);
v_s_646_ = l_Lean_Parser_ParserState_popSyntax(v___y_642_);
v_s_647_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_636_, v_s_646_);
v_s_648_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_644_, v_s_647_);
v___x_649_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_650_ = l_Lean_Parser_ParserState_mkNode(v_s_648_, v___x_649_, v_iniSz_631_);
lean_dec(v_iniSz_631_);
return v___x_650_;
}
}
v___jp_651_:
{
if (v___y_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_655_ = l_Lean_Parser_ParserState_stackSize(v___y_653_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_iniSz_631_, v___x_656_);
v___x_658_ = lean_nat_dec_eq(v___x_655_, v___x_657_);
lean_dec(v___x_657_);
lean_dec(v___x_655_);
if (v___x_658_ == 0)
{
if (v___y_652_ == 0)
{
v___y_642_ = v___y_653_;
goto v___jp_641_;
}
else
{
v___y_638_ = v___y_653_;
goto v___jp_637_;
}
}
else
{
v___y_642_ = v___y_653_;
goto v___jp_641_;
}
}
else
{
v___y_638_ = v___y_653_;
goto v___jp_637_;
}
}
v___jp_659_:
{
if (v___y_660_ == 0)
{
uint8_t v___x_661_; 
lean_inc(v_pBack_636_);
v___x_661_ = l_Lean_Syntax_isAntiquots(v_pBack_636_);
if (v___x_661_ == 0)
{
lean_dec(v_pBack_636_);
lean_dec(v_pos_635_);
lean_dec(v_iniSz_631_);
lean_dec(v_pos_630_);
lean_dec_ref(v_c_628_);
lean_dec_ref(v_q_626_);
return v_s_632_;
}
else
{
lean_object* v_s_662_; lean_object* v_s_663_; lean_object* v_pos_664_; lean_object* v_errorMsg_665_; uint8_t v___x_666_; 
v_s_662_ = l_Lean_Parser_ParserState_restore(v_s_632_, v_iniSz_631_, v_pos_630_);
v_s_663_ = lean_apply_2(v_q_626_, v_c_628_, v_s_662_);
v_pos_664_ = lean_ctor_get(v_s_663_, 2);
lean_inc(v_pos_664_);
v_errorMsg_665_ = lean_ctor_get(v_s_663_, 4);
lean_inc(v_errorMsg_665_);
v___x_666_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_665_, v_errorMsg_633_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_pos_664_);
v___x_667_ = l_Lean_Parser_ParserState_restore(v_s_663_, v_iniSz_631_, v_pos_635_);
lean_dec(v_iniSz_631_);
v___x_668_ = l_Lean_Parser_ParserState_pushSyntax(v___x_667_, v_pBack_636_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_lt(v_pos_635_, v_pos_664_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_lt(v_pos_664_, v_pos_635_);
lean_dec(v_pos_664_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 2;
v___x_672_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_627_, v___x_671_);
if (v___x_672_ == 0)
{
v___y_652_ = v___x_666_;
v___y_653_ = v_s_663_;
v___y_654_ = v___x_666_;
goto v___jp_651_;
}
else
{
v___y_652_ = v___x_666_;
v___y_653_ = v_s_663_;
v___y_654_ = v___x_670_;
goto v___jp_651_;
}
}
else
{
v___y_652_ = v___x_666_;
v___y_653_ = v_s_663_;
v___y_654_ = v___x_670_;
goto v___jp_651_;
}
}
else
{
lean_dec(v_pos_664_);
lean_dec(v_pBack_636_);
lean_dec(v_pos_635_);
lean_dec(v_iniSz_631_);
return v_s_663_;
}
}
}
}
else
{
lean_dec(v_pBack_636_);
lean_dec(v_pos_635_);
lean_dec(v_iniSz_631_);
lean_dec(v_pos_630_);
lean_dec_ref(v_c_628_);
lean_dec_ref(v_q_626_);
return v_s_632_;
}
}
}
else
{
lean_object* v_pos_679_; lean_object* v_val_680_; uint8_t v___x_681_; 
v_pos_679_ = lean_ctor_get(v_s_632_, 2);
lean_inc(v_pos_679_);
v_val_680_ = lean_ctor_get(v_errorMsg_633_, 0);
lean_inc(v_val_680_);
lean_dec_ref(v_errorMsg_633_);
v___x_681_ = lean_nat_dec_eq(v_pos_679_, v_pos_630_);
lean_dec(v_pos_679_);
if (v___x_681_ == 0)
{
lean_dec(v_val_680_);
lean_dec(v_iniSz_631_);
lean_dec(v_pos_630_);
lean_dec_ref(v_c_628_);
lean_dec_ref(v_q_626_);
return v_s_632_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc(v_pos_630_);
v___x_682_ = l_Lean_Parser_ParserState_restore(v_s_632_, v_iniSz_631_, v_pos_630_);
lean_dec(v_iniSz_631_);
v___x_683_ = lean_apply_2(v_q_626_, v_c_628_, v___x_682_);
v___x_684_ = l_Lean_Parser_mergeOrElseErrors(v___x_683_, v_val_680_, v_pos_630_, v___x_681_);
lean_dec(v_pos_630_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_685_, lean_object* v_q_686_, lean_object* v_antiquotBehavior_687_, lean_object* v_c_688_, lean_object* v_s_689_){
_start:
{
uint8_t v_antiquotBehavior_boxed_690_; lean_object* v_res_691_; 
v_antiquotBehavior_boxed_690_ = lean_unbox(v_antiquotBehavior_687_);
v_res_691_ = l_Lean_Parser_orelseFnCore(v_p_685_, v_q_686_, v_antiquotBehavior_boxed_690_, v_c_688_, v_s_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_692_, lean_object* v_q_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
uint8_t v___x_696_; lean_object* v___x_697_; 
v___x_696_ = 2;
v___x_697_ = l_Lean_Parser_orelseFnCore(v_p_692_, v_q_693_, v___x_696_, v_a_694_, v_a_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_698_, lean_object* v_q_699_){
_start:
{
lean_object* v_collectTokens_700_; lean_object* v_collectKinds_701_; lean_object* v_firstTokens_702_; lean_object* v_collectTokens_703_; lean_object* v_collectKinds_704_; lean_object* v_firstTokens_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_715_; 
v_collectTokens_700_ = lean_ctor_get(v_p_698_, 0);
lean_inc_ref(v_collectTokens_700_);
v_collectKinds_701_ = lean_ctor_get(v_p_698_, 1);
lean_inc_ref(v_collectKinds_701_);
v_firstTokens_702_ = lean_ctor_get(v_p_698_, 2);
lean_inc(v_firstTokens_702_);
lean_dec_ref(v_p_698_);
v_collectTokens_703_ = lean_ctor_get(v_q_699_, 0);
v_collectKinds_704_ = lean_ctor_get(v_q_699_, 1);
v_firstTokens_705_ = lean_ctor_get(v_q_699_, 2);
v_isSharedCheck_715_ = !lean_is_exclusive(v_q_699_);
if (v_isSharedCheck_715_ == 0)
{
v___x_707_ = v_q_699_;
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_firstTokens_705_);
lean_inc(v_collectKinds_704_);
lean_inc(v_collectTokens_703_);
lean_dec(v_q_699_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___f_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_709_, 0, v_collectKinds_704_);
lean_closure_set(v___f_709_, 1, v_collectKinds_701_);
v___f_710_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_710_, 0, v_collectTokens_703_);
lean_closure_set(v___f_710_, 1, v_collectTokens_700_);
v___x_711_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_702_, v_firstTokens_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 2, v___x_711_);
lean_ctor_set(v___x_707_, 1, v___f_709_);
lean_ctor_set(v___x_707_, 0, v___f_710_);
v___x_713_ = v___x_707_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___f_710_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___f_709_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_716_, lean_object* v_p2_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_apply_1(v_p2_717_, v___x_720_);
v___x_722_ = l_Lean_Parser_orelseFn(v_p1_716_, v___x_721_, v___y_718_, v___y_719_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_725_, lean_object* v_q_726_){
_start:
{
lean_object* v_info_727_; lean_object* v_fn_728_; lean_object* v_info_729_; lean_object* v_fn_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_739_; 
v_info_727_ = lean_ctor_get(v_p_725_, 0);
lean_inc_ref(v_info_727_);
v_fn_728_ = lean_ctor_get(v_p_725_, 1);
lean_inc_ref(v_fn_728_);
lean_dec_ref(v_p_725_);
v_info_729_ = lean_ctor_get(v_q_726_, 0);
v_fn_730_ = lean_ctor_get(v_q_726_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_q_726_);
if (v_isSharedCheck_739_ == 0)
{
v___x_732_ = v_q_726_;
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_fn_730_);
lean_inc(v_info_729_);
lean_dec(v_q_726_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = l_Lean_Parser_orelseInfo(v_info_727_, v_info_729_);
v___x_735_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_735_, 0, v_fn_728_);
lean_closure_set(v___x_735_, 1, v_fn_730_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_735_);
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((lean_object*)(l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_748_ = ((lean_object*)(l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_749_ = l_Lean_addBuiltinDocString(v___x_747_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_752_, lean_object* v_b_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_box(0);
v___x_755_ = lean_apply_1(v_b_753_, v___x_754_);
v___x_756_ = l_Lean_Parser_orelse(v_a_752_, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_759_){
_start:
{
lean_object* v_collectTokens_760_; lean_object* v_collectKinds_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_collectTokens_760_ = lean_ctor_get(v_info_759_, 0);
v_collectKinds_761_ = lean_ctor_get(v_info_759_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_info_759_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_info_759_, 2);
lean_dec(v_unused_770_);
v___x_763_ = v_info_759_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_collectKinds_761_);
lean_inc(v_collectTokens_760_);
lean_dec(v_info_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_box(1);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_collectTokens_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_collectKinds_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_771_, lean_object* v_c_772_, lean_object* v_s_773_){
_start:
{
lean_object* v_pos_774_; lean_object* v___x_775_; lean_object* v_errorMsg_776_; 
v_pos_774_ = lean_ctor_get(v_s_773_, 2);
lean_inc(v_pos_774_);
v___x_775_ = lean_apply_2(v_p_771_, v_c_772_, v_s_773_);
v_errorMsg_776_ = lean_ctor_get(v___x_775_, 4);
lean_inc(v_errorMsg_776_);
if (lean_obj_tag(v_errorMsg_776_) == 1)
{
lean_object* v_stxStack_777_; lean_object* v_lhsPrec_778_; lean_object* v_cache_779_; lean_object* v_recoveredErrors_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_stxStack_777_ = lean_ctor_get(v___x_775_, 0);
v_lhsPrec_778_ = lean_ctor_get(v___x_775_, 1);
v_cache_779_ = lean_ctor_get(v___x_775_, 3);
v_recoveredErrors_780_ = lean_ctor_get(v___x_775_, 5);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_788_ = lean_ctor_get(v___x_775_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v___x_775_, 2);
lean_dec(v_unused_789_);
v___x_782_ = v___x_775_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_recoveredErrors_780_);
lean_inc(v_cache_779_);
lean_inc(v_lhsPrec_778_);
lean_inc(v_stxStack_777_);
lean_dec(v___x_775_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 2, v_pos_774_);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_stxStack_777_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_lhsPrec_778_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_pos_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_cache_779_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_errorMsg_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 5, v_recoveredErrors_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_dec(v_errorMsg_776_);
lean_dec(v_pos_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_790_){
_start:
{
lean_object* v_info_791_; lean_object* v_fn_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_info_791_ = lean_ctor_get(v_p_790_, 0);
v_fn_792_ = lean_ctor_get(v_p_790_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_p_790_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v_p_790_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_fn_792_);
lean_inc(v_info_791_);
lean_dec(v_p_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_796_, 0, v_fn_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_info_791_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((lean_object*)(l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_809_ = ((lean_object*)(l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_810_ = l_Lean_addBuiltinDocString(v___x_808_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_initialPos_815_; lean_object* v_initialSize_816_; lean_object* v_initialPos_817_; lean_object* v_initialSize_818_; uint8_t v___x_819_; 
v_initialPos_815_ = lean_ctor_get(v_x_813_, 0);
v_initialSize_816_ = lean_ctor_get(v_x_813_, 1);
v_initialPos_817_ = lean_ctor_get(v_x_814_, 0);
v_initialSize_818_ = lean_ctor_get(v_x_814_, 1);
v___x_819_ = lean_nat_dec_eq(v_initialPos_815_, v_initialPos_817_);
if (v___x_819_ == 0)
{
return v___x_819_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = lean_nat_dec_eq(v_initialSize_816_, v_initialSize_818_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_821_, v_x_822_);
lean_dec_ref(v_x_822_);
lean_dec_ref(v_x_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v_initialPos_829_; lean_object* v_initialSize_830_; lean_object* v_initialPos_831_; lean_object* v_initialSize_832_; uint8_t v___x_833_; 
v_initialPos_829_ = lean_ctor_get(v_x_827_, 0);
v_initialSize_830_ = lean_ctor_get(v_x_827_, 1);
v_initialPos_831_ = lean_ctor_get(v_x_828_, 0);
v_initialSize_832_ = lean_ctor_get(v_x_828_, 1);
v___x_833_ = lean_nat_dec_eq(v_initialPos_829_, v_initialPos_831_);
if (v___x_833_ == 0)
{
return v___x_833_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_eq(v_initialSize_830_, v_initialSize_832_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_835_, v_x_836_);
lean_dec_ref(v_x_836_);
lean_dec_ref(v_x_835_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_842_, v_x_843_);
lean_dec_ref(v_x_843_);
lean_dec_ref(v_x_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_unsigned_to_nat(14u);
v___x_860_ = lean_nat_to_int(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(15u);
v___x_874_ = lean_nat_to_int(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_876_ = lean_string_length(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_878_ = lean_nat_to_int(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_881_){
_start:
{
lean_object* v_initialPos_882_; lean_object* v_initialSize_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_921_; 
v_initialPos_882_ = lean_ctor_get(v_x_881_, 0);
v_initialSize_883_ = lean_ctor_get(v_x_881_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_921_ == 0)
{
v___x_885_ = v_x_881_;
v_isShared_886_ = v_isSharedCheck_921_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_initialSize_883_);
lean_inc(v_initialPos_882_);
lean_dec(v_x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_921_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_887_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_888_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_889_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_890_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_891_ = l_Nat_reprFast(v_initialPos_882_);
v___x_892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 5);
lean_ctor_set(v___x_885_, 1, v___x_892_);
lean_ctor_set(v___x_885_, 0, v___x_890_);
v___x_894_ = v___x_885_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_920_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_895_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_889_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = 0;
v___x_899_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*1, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_888_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_box(1);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_887_);
v___x_908_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_909_ = l_Nat_reprFast(v_initialSize_883_);
v___x_910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_908_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_898_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_907_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_915_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_913_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_895_);
v___x_918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_914_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*1, v___x_898_);
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_922_, lean_object* v_prec_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_925_, lean_object* v_prec_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_925_, v_prec_926_);
lean_dec(v_prec_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_930_, lean_object* v_recover_931_, lean_object* v_c_932_, lean_object* v_s_933_){
_start:
{
lean_object* v_stxStack_934_; lean_object* v_pos_935_; lean_object* v_s_936_; lean_object* v_errorMsg_937_; 
v_stxStack_934_ = lean_ctor_get(v_s_933_, 0);
lean_inc_ref(v_stxStack_934_);
v_pos_935_ = lean_ctor_get(v_s_933_, 2);
lean_inc(v_pos_935_);
lean_inc_ref(v_c_932_);
v_s_936_ = lean_apply_2(v_p_930_, v_c_932_, v_s_933_);
v_errorMsg_937_ = lean_ctor_get(v_s_936_, 4);
lean_inc(v_errorMsg_937_);
if (lean_obj_tag(v_errorMsg_937_) == 1)
{
lean_object* v_stxStack_938_; lean_object* v_lhsPrec_939_; lean_object* v_pos_940_; lean_object* v_cache_941_; lean_object* v_recoveredErrors_942_; lean_object* v_val_943_; lean_object* v_iniSz_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_s_x27_948_; lean_object* v_stxStack_949_; lean_object* v_pos_950_; lean_object* v_errorMsg_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_962_; 
v_stxStack_938_ = lean_ctor_get(v_s_936_, 0);
lean_inc_ref(v_stxStack_938_);
v_lhsPrec_939_ = lean_ctor_get(v_s_936_, 1);
lean_inc(v_lhsPrec_939_);
v_pos_940_ = lean_ctor_get(v_s_936_, 2);
lean_inc(v_pos_940_);
v_cache_941_ = lean_ctor_get(v_s_936_, 3);
lean_inc_ref(v_cache_941_);
v_recoveredErrors_942_ = lean_ctor_get(v_s_936_, 5);
lean_inc_ref(v_recoveredErrors_942_);
v_val_943_ = lean_ctor_get(v_errorMsg_937_, 0);
lean_inc(v_val_943_);
lean_dec_ref(v_errorMsg_937_);
v_iniSz_944_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_934_);
lean_dec_ref(v_stxStack_934_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_pos_935_);
lean_ctor_set(v___x_945_, 1, v_iniSz_944_);
v___x_946_ = lean_box(0);
lean_inc_ref(v_recoveredErrors_942_);
lean_inc_ref(v_cache_941_);
lean_inc(v_lhsPrec_939_);
v___x_947_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_947_, 0, v_stxStack_938_);
lean_ctor_set(v___x_947_, 1, v_lhsPrec_939_);
lean_ctor_set(v___x_947_, 2, v_pos_940_);
lean_ctor_set(v___x_947_, 3, v_cache_941_);
lean_ctor_set(v___x_947_, 4, v___x_946_);
lean_ctor_set(v___x_947_, 5, v_recoveredErrors_942_);
v_s_x27_948_ = lean_apply_3(v_recover_931_, v___x_945_, v_c_932_, v___x_947_);
v_stxStack_949_ = lean_ctor_get(v_s_x27_948_, 0);
v_pos_950_ = lean_ctor_get(v_s_x27_948_, 2);
v_errorMsg_951_ = lean_ctor_get(v_s_x27_948_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v_s_x27_948_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; 
v_unused_963_ = lean_ctor_get(v_s_x27_948_, 5);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_s_x27_948_, 3);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_s_x27_948_, 1);
lean_dec(v_unused_965_);
v___x_953_ = v_s_x27_948_;
v_isShared_954_ = v_isSharedCheck_962_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_errorMsg_951_);
lean_inc(v_pos_950_);
lean_inc(v_stxStack_949_);
lean_dec(v_s_x27_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_962_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_951_, v___x_946_);
if (v___x_955_ == 0)
{
lean_del_object(v___x_953_);
lean_dec(v_pos_950_);
lean_dec_ref(v_stxStack_949_);
lean_dec(v_val_943_);
lean_dec_ref(v_recoveredErrors_942_);
lean_dec_ref(v_cache_941_);
lean_dec(v_lhsPrec_939_);
return v_s_936_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec_ref(v_s_936_);
lean_inc_ref(v_stxStack_949_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_stxStack_949_);
lean_ctor_set(v___x_956_, 1, v_val_943_);
lean_inc(v_pos_950_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_pos_950_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_array_push(v_recoveredErrors_942_, v___x_957_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 5, v___x_958_);
lean_ctor_set(v___x_953_, 4, v___x_946_);
lean_ctor_set(v___x_953_, 3, v_cache_941_);
lean_ctor_set(v___x_953_, 1, v_lhsPrec_939_);
v___x_960_ = v___x_953_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_stxStack_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_lhsPrec_939_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_pos_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_cache_941_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 5, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_dec(v_errorMsg_937_);
lean_dec(v_pos_935_);
lean_dec_ref(v_stxStack_934_);
lean_dec_ref(v_c_932_);
lean_dec_ref(v_recover_931_);
return v_s_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_966_, lean_object* v_s_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_970_; lean_object* v_fn_971_; lean_object* v___x_972_; 
v___x_970_ = lean_apply_1(v_handler_966_, v_s_967_);
v_fn_971_ = lean_ctor_get(v___x_970_, 1);
lean_inc_ref(v_fn_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = lean_apply_2(v_fn_971_, v___y_968_, v___y_969_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_973_, lean_object* v_handler_974_){
_start:
{
lean_object* v_info_975_; lean_object* v_fn_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_985_; 
v_info_975_ = lean_ctor_get(v_parser_973_, 0);
v_fn_976_ = lean_ctor_get(v_parser_973_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_parser_973_);
if (v_isSharedCheck_985_ == 0)
{
v___x_978_ = v_parser_973_;
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_fn_976_);
lean_inc(v_info_975_);
lean_dec(v_parser_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___f_980_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_980_, 0, v_handler_974_);
v___x_981_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_981_, 0, v_fn_976_);
lean_closure_set(v___x_981_, 1, v___f_980_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_info_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_994_ = ((lean_object*)(l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_995_ = l_Lean_addBuiltinDocString(v___x_993_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_998_, lean_object* v_x_999_){
_start:
{
lean_inc_ref(v_handler_998_);
return v_handler_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Parser_recover___lam__0(v_handler_1000_, v_x_1001_);
lean_dec_ref(v_x_1001_);
lean_dec_ref(v_handler_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1003_, lean_object* v_handler_1004_){
_start:
{
lean_object* v___f_1005_; lean_object* v___x_1006_; 
v___f_1005_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1005_, 0, v_handler_1004_);
v___x_1006_ = l_Lean_Parser_recover_x27(v_parser_1003_, v___f_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((lean_object*)(l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1015_ = ((lean_object*)(l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1016_ = l_Lean_addBuiltinDocString(v___x_1014_, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1022_, lean_object* v_c_1023_, lean_object* v_s_1024_){
_start:
{
lean_object* v_pos_1025_; lean_object* v_iniSz_1026_; lean_object* v___y_1028_; lean_object* v_s_1031_; lean_object* v_pos_1032_; lean_object* v_errorMsg_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_pos_1025_ = lean_ctor_get(v_s_1024_, 2);
lean_inc(v_pos_1025_);
v_iniSz_1026_ = l_Lean_Parser_ParserState_stackSize(v_s_1024_);
v_s_1031_ = lean_apply_2(v_p_1022_, v_c_1023_, v_s_1024_);
v_pos_1032_ = lean_ctor_get(v_s_1031_, 2);
lean_inc(v_pos_1032_);
v_errorMsg_1033_ = lean_ctor_get(v_s_1031_, 4);
lean_inc(v_errorMsg_1033_);
v___x_1034_ = lean_box(0);
v___x_1035_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_nat_dec_eq(v_pos_1032_, v_pos_1025_);
lean_dec(v_pos_1032_);
if (v___x_1036_ == 0)
{
lean_dec(v_pos_1025_);
v___y_1028_ = v_s_1031_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Parser_ParserState_restore(v_s_1031_, v_iniSz_1026_, v_pos_1025_);
v___y_1028_ = v___x_1037_;
goto v___jp_1027_;
}
}
else
{
lean_dec(v_pos_1032_);
lean_dec(v_pos_1025_);
v___y_1028_ = v_s_1031_;
goto v___jp_1027_;
}
v___jp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1030_ = l_Lean_Parser_ParserState_mkNode(v___y_1028_, v___x_1029_, v_iniSz_1026_);
lean_dec(v_iniSz_1026_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1038_){
_start:
{
lean_object* v_collectTokens_1039_; lean_object* v_collectKinds_1040_; lean_object* v_firstTokens_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_collectTokens_1039_ = lean_ctor_get(v_p_1038_, 0);
v_collectKinds_1040_ = lean_ctor_get(v_p_1038_, 1);
v_firstTokens_1041_ = lean_ctor_get(v_p_1038_, 2);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_p_1038_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v_p_1038_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_firstTokens_1041_);
lean_inc(v_collectKinds_1040_);
lean_inc(v_collectTokens_1039_);
lean_dec(v_p_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 2, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_collectTokens_1039_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_collectKinds_1040_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1050_){
_start:
{
lean_object* v_info_1051_; lean_object* v_fn_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v_info_1051_ = lean_ctor_get(v_p_1050_, 0);
v_fn_1052_ = lean_ctor_get(v_p_1050_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_p_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v_p_1050_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_fn_1052_);
lean_inc(v_info_1051_);
lean_dec(v_p_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = l_Lean_Parser_optionalInfo(v_info_1051_);
v___x_1057_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1057_, 0, v_fn_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1057_);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1062_, lean_object* v_c_1063_, lean_object* v_s_1064_){
_start:
{
lean_object* v_pos_1065_; lean_object* v_iniSz_1066_; lean_object* v_s_1067_; lean_object* v_errorMsg_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_pos_1065_ = lean_ctor_get(v_s_1064_, 2);
lean_inc(v_pos_1065_);
v_iniSz_1066_ = l_Lean_Parser_ParserState_stackSize(v_s_1064_);
v_s_1067_ = lean_apply_2(v_p_1062_, v_c_1063_, v_s_1064_);
v_errorMsg_1068_ = lean_ctor_get(v_s_1067_, 4);
lean_inc(v_errorMsg_1068_);
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_iniSz_1066_);
lean_dec(v_pos_1065_);
return v_s_1067_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Parser_ParserState_restore(v_s_1067_, v_iniSz_1066_, v_pos_1065_);
lean_dec(v_iniSz_1066_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1072_){
_start:
{
lean_object* v_info_1073_; lean_object* v_fn_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_info_1073_ = lean_ctor_get(v_p_1072_, 0);
v_fn_1074_ = lean_ctor_get(v_p_1072_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_p_1072_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v_p_1072_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_fn_1074_);
lean_inc(v_info_1073_);
lean_dec(v_p_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1078_, 0, v_fn_1074_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_info_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = ((lean_object*)(l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1091_ = ((lean_object*)(l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1092_ = l_Lean_addBuiltinDocString(v___x_1090_, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1096_, lean_object* v_msg_1097_, lean_object* v_c_1098_, lean_object* v_s_1099_){
_start:
{
lean_object* v_pos_1100_; lean_object* v_iniSz_1101_; lean_object* v_s_1102_; lean_object* v_errorMsg_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_pos_1100_ = lean_ctor_get(v_s_1099_, 2);
lean_inc(v_pos_1100_);
v_iniSz_1101_ = l_Lean_Parser_ParserState_stackSize(v_s_1099_);
v_s_1102_ = lean_apply_2(v_p_1096_, v_c_1098_, v_s_1099_);
v_errorMsg_1103_ = lean_ctor_get(v_s_1102_, 4);
lean_inc(v_errorMsg_1103_);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Parser_ParserState_restore(v_s_1102_, v_iniSz_1101_, v_pos_1100_);
lean_dec(v_iniSz_1101_);
return v___x_1106_;
}
else
{
lean_object* v_s_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_s_1107_ = l_Lean_Parser_ParserState_restore(v_s_1102_, v_iniSz_1101_, v_pos_1100_);
lean_dec(v_iniSz_1101_);
v___x_1108_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1109_ = lean_string_append(v___x_1108_, v_msg_1097_);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1107_, v___x_1109_, v___x_1110_, v___x_1105_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1112_, lean_object* v_msg_1113_, lean_object* v_c_1114_, lean_object* v_s_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Parser_notFollowedByFn(v_p_1112_, v_msg_1113_, v_c_1114_, v_s_1115_);
lean_dec_ref(v_msg_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1117_, lean_object* v_msg_1118_){
_start:
{
lean_object* v_fn_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1128_; 
v_fn_1119_ = lean_ctor_get(v_p_1117_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_p_1117_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_p_1117_, 0);
lean_dec(v_unused_1129_);
v___x_1121_ = v_p_1117_;
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_fn_1119_);
lean_dec(v_p_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1123_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1124_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1124_, 0, v_fn_1119_);
lean_closure_set(v___x_1124_, 1, v_msg_1118_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1124_);
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((lean_object*)(l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1138_ = ((lean_object*)(l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1139_ = l_Lean_addBuiltinDocString(v___x_1137_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1143_, lean_object* v_c_1144_, lean_object* v_s_1145_){
_start:
{
lean_object* v_pos_1146_; lean_object* v_iniSz_1147_; lean_object* v_s_1148_; lean_object* v_pos_1149_; lean_object* v_errorMsg_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v_pos_1146_ = lean_ctor_get(v_s_1145_, 2);
lean_inc(v_pos_1146_);
v_iniSz_1147_ = l_Lean_Parser_ParserState_stackSize(v_s_1145_);
lean_inc_ref(v_p_1143_);
lean_inc_ref(v_c_1144_);
v_s_1148_ = lean_apply_2(v_p_1143_, v_c_1144_, v_s_1145_);
v_pos_1149_ = lean_ctor_get(v_s_1148_, 2);
lean_inc(v_pos_1149_);
v_errorMsg_1150_ = lean_ctor_get(v_s_1148_, 4);
lean_inc(v_errorMsg_1150_);
v___x_1151_ = lean_box(0);
v___x_1152_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; 
lean_dec_ref(v_c_1144_);
lean_dec_ref(v_p_1143_);
v___x_1153_ = lean_nat_dec_eq(v_pos_1146_, v_pos_1149_);
lean_dec(v_pos_1149_);
if (v___x_1153_ == 0)
{
lean_dec(v_iniSz_1147_);
lean_dec(v_pos_1146_);
return v_s_1148_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Parser_ParserState_restore(v_s_1148_, v_iniSz_1147_, v_pos_1146_);
lean_dec(v_iniSz_1147_);
return v___x_1154_;
}
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_nat_dec_eq(v_pos_1146_, v_pos_1149_);
lean_dec(v_pos_1149_);
lean_dec(v_pos_1146_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_add(v_iniSz_1147_, v___x_1156_);
v___x_1158_ = l_Lean_Parser_ParserState_stackSize(v_s_1148_);
v___x_1159_ = lean_nat_dec_lt(v___x_1157_, v___x_1158_);
lean_dec(v___x_1158_);
lean_dec(v___x_1157_);
if (v___x_1159_ == 0)
{
lean_dec(v_iniSz_1147_);
v_s_1145_ = v_s_1148_;
goto _start;
}
else
{
lean_object* v___x_1161_; lean_object* v_s_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1162_ = l_Lean_Parser_ParserState_mkNode(v_s_1148_, v___x_1161_, v_iniSz_1147_);
lean_dec(v_iniSz_1147_);
v_s_1145_ = v_s_1162_;
goto _start;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_iniSz_1147_);
lean_dec_ref(v_c_1144_);
lean_dec_ref(v_p_1143_);
v___x_1164_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1165_ = lean_box(0);
v___x_1166_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1148_, v___x_1164_, v___x_1165_, v___x_1152_);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1167_, lean_object* v_c_1168_, lean_object* v_s_1169_){
_start:
{
lean_object* v_iniSz_1170_; lean_object* v_s_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_iniSz_1170_ = l_Lean_Parser_ParserState_stackSize(v_s_1169_);
v_s_1171_ = l_Lean_Parser_manyAux(v_p_1167_, v_c_1168_, v_s_1169_);
v___x_1172_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1173_ = l_Lean_Parser_ParserState_mkNode(v_s_1171_, v___x_1172_, v_iniSz_1170_);
lean_dec(v_iniSz_1170_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1174_){
_start:
{
lean_object* v_info_1175_; lean_object* v_fn_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
v_info_1175_ = lean_ctor_get(v_p_1174_, 0);
v_fn_1176_ = lean_ctor_get(v_p_1174_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_p_1174_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1178_ = v_p_1174_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_fn_1176_);
lean_inc(v_info_1175_);
lean_dec(v_p_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = l_Lean_Parser_noFirstTokenInfo(v_info_1175_);
v___x_1181_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1181_, 0, v_fn_1176_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1181_);
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1186_, lean_object* v_c_1187_, lean_object* v_s_1188_){
_start:
{
lean_object* v_iniSz_1189_; lean_object* v___x_1190_; lean_object* v_s_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_iniSz_1189_ = l_Lean_Parser_ParserState_stackSize(v_s_1188_);
lean_inc_ref(v_p_1186_);
v___x_1190_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1190_, 0, v_p_1186_);
v_s_1191_ = l_Lean_Parser_andthenFn(v_p_1186_, v___x_1190_, v_c_1187_, v_s_1188_);
v___x_1192_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1193_ = l_Lean_Parser_ParserState_mkNode(v_s_1191_, v___x_1192_, v_iniSz_1189_);
lean_dec(v_iniSz_1189_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1194_){
_start:
{
lean_object* v_info_1195_; lean_object* v_fn_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1204_; 
v_info_1195_ = lean_ctor_get(v_p_1194_, 0);
v_fn_1196_ = lean_ctor_get(v_p_1194_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_p_1194_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1198_ = v_p_1194_;
v_isShared_1199_ = v_isSharedCheck_1204_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_fn_1196_);
lean_inc(v_info_1195_);
lean_dec(v_p_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1204_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1200_, 0, v_fn_1196_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v___x_1200_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_info_1195_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1205_, lean_object* v_sep_1206_, uint8_t v_allowTrailingSep_1207_, lean_object* v_iniSz_1208_, uint8_t v_pOpt_1209_, lean_object* v_c_1210_, lean_object* v_s_1211_){
_start:
{
lean_object* v_s_1213_; lean_object* v_pos_1214_; lean_object* v_pos_1231_; lean_object* v_sz_1232_; lean_object* v_s_1233_; lean_object* v_pos_1234_; lean_object* v_errorMsg_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_pos_1231_ = lean_ctor_get(v_s_1211_, 2);
lean_inc(v_pos_1231_);
v_sz_1232_ = l_Lean_Parser_ParserState_stackSize(v_s_1211_);
lean_inc_ref(v_p_1205_);
lean_inc_ref(v_c_1210_);
v_s_1233_ = lean_apply_2(v_p_1205_, v_c_1210_, v_s_1211_);
v_pos_1234_ = lean_ctor_get(v_s_1233_, 2);
lean_inc(v_pos_1234_);
v_errorMsg_1235_ = lean_ctor_get(v_s_1233_, 4);
lean_inc(v_errorMsg_1235_);
v___x_1236_ = lean_box(0);
v___x_1237_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; 
lean_dec_ref(v_c_1210_);
lean_dec_ref(v_sep_1206_);
lean_dec_ref(v_p_1205_);
v___x_1238_ = lean_nat_dec_lt(v_pos_1231_, v_pos_1234_);
lean_dec(v_pos_1234_);
if (v___x_1238_ == 0)
{
if (v_pOpt_1209_ == 0)
{
lean_object* v___x_1239_; lean_object* v_s_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v_sz_1232_);
lean_dec(v_pos_1231_);
v___x_1239_ = lean_box(0);
v_s_1240_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1233_, v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1242_ = l_Lean_Parser_ParserState_mkNode(v_s_1240_, v___x_1241_, v_iniSz_1208_);
return v___x_1242_;
}
else
{
lean_object* v_s_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_s_1243_ = l_Lean_Parser_ParserState_restore(v_s_1233_, v_sz_1232_, v_pos_1231_);
lean_dec(v_sz_1232_);
v___x_1244_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1245_ = l_Lean_Parser_ParserState_mkNode(v_s_1243_, v___x_1244_, v_iniSz_1208_);
return v___x_1245_;
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec(v_sz_1232_);
lean_dec(v_pos_1231_);
v___x_1246_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1247_ = l_Lean_Parser_ParserState_mkNode(v_s_1233_, v___x_1246_, v_iniSz_1208_);
return v___x_1247_;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_dec(v_pos_1231_);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_sz_1232_, v___x_1248_);
v___x_1250_ = l_Lean_Parser_ParserState_stackSize(v_s_1233_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1249_);
if (v___x_1251_ == 0)
{
lean_dec(v_sz_1232_);
v_s_1213_ = v_s_1233_;
v_pos_1214_ = v_pos_1234_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1252_; lean_object* v_s_1253_; lean_object* v_pos_1254_; 
lean_dec(v_pos_1234_);
v___x_1252_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1253_ = l_Lean_Parser_ParserState_mkNode(v_s_1233_, v___x_1252_, v_sz_1232_);
lean_dec(v_sz_1232_);
v_pos_1254_ = lean_ctor_get(v_s_1253_, 2);
lean_inc(v_pos_1254_);
v_s_1213_ = v_s_1253_;
v_pos_1214_ = v_pos_1254_;
goto v___jp_1212_;
}
}
v___jp_1212_:
{
lean_object* v_sz_1215_; lean_object* v_s_1216_; lean_object* v_errorMsg_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_sz_1215_ = l_Lean_Parser_ParserState_stackSize(v_s_1213_);
lean_inc_ref(v_sep_1206_);
lean_inc_ref(v_c_1210_);
v_s_1216_ = lean_apply_2(v_sep_1206_, v_c_1210_, v_s_1213_);
v_errorMsg_1217_ = lean_ctor_get(v_s_1216_, 4);
lean_inc(v_errorMsg_1217_);
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v_s_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v_c_1210_);
lean_dec_ref(v_sep_1206_);
lean_dec_ref(v_p_1205_);
v_s_1220_ = l_Lean_Parser_ParserState_restore(v_s_1216_, v_sz_1215_, v_pos_1214_);
lean_dec(v_sz_1215_);
v___x_1221_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1222_ = l_Lean_Parser_ParserState_mkNode(v_s_1220_, v___x_1221_, v_iniSz_1208_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
lean_dec(v_pos_1214_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_add(v_sz_1215_, v___x_1223_);
v___x_1225_ = l_Lean_Parser_ParserState_stackSize(v_s_1216_);
v___x_1226_ = lean_nat_dec_lt(v___x_1224_, v___x_1225_);
lean_dec(v___x_1225_);
lean_dec(v___x_1224_);
if (v___x_1226_ == 0)
{
lean_dec(v_sz_1215_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1207_;
lean_object* _tmp_6 = v_s_1216_;
v_pOpt_1209_ = _tmp_4;
v_s_1211_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1228_; lean_object* v_s_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1229_ = l_Lean_Parser_ParserState_mkNode(v_s_1216_, v___x_1228_, v_sz_1215_);
lean_dec(v_sz_1215_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1207_;
lean_object* _tmp_6 = v_s_1229_;
v_pOpt_1209_ = _tmp_4;
v_s_1211_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1255_, lean_object* v_sep_1256_, lean_object* v_allowTrailingSep_1257_, lean_object* v_iniSz_1258_, lean_object* v_pOpt_1259_, lean_object* v_c_1260_, lean_object* v_s_1261_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1262_; uint8_t v_pOpt_boxed_1263_; lean_object* v_res_1264_; 
v_allowTrailingSep_boxed_1262_ = lean_unbox(v_allowTrailingSep_1257_);
v_pOpt_boxed_1263_ = lean_unbox(v_pOpt_1259_);
v_res_1264_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1255_, v_sep_1256_, v_allowTrailingSep_boxed_1262_, v_iniSz_1258_, v_pOpt_boxed_1263_, v_c_1260_, v_s_1261_);
lean_dec(v_iniSz_1258_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1265_, lean_object* v_sep_1266_, uint8_t v_allowTrailingSep_1267_, lean_object* v_iniSz_1268_, uint8_t v_pOpt_1269_, lean_object* v_c_1270_, lean_object* v_s_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1265_, v_sep_1266_, v_allowTrailingSep_1267_, v_iniSz_1268_, v_pOpt_1269_, v_c_1270_, v_s_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1273_, lean_object* v_sep_1274_, lean_object* v_allowTrailingSep_1275_, lean_object* v_iniSz_1276_, lean_object* v_pOpt_1277_, lean_object* v_c_1278_, lean_object* v_s_1279_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1280_; uint8_t v_pOpt_boxed_1281_; lean_object* v_res_1282_; 
v_allowTrailingSep_boxed_1280_ = lean_unbox(v_allowTrailingSep_1275_);
v_pOpt_boxed_1281_ = lean_unbox(v_pOpt_1277_);
v_res_1282_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1273_, v_sep_1274_, v_allowTrailingSep_boxed_1280_, v_iniSz_1276_, v_pOpt_boxed_1281_, v_c_1278_, v_s_1279_);
lean_dec(v_iniSz_1276_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1283_, lean_object* v_p_1284_, lean_object* v_sep_1285_, lean_object* v_c_1286_, lean_object* v_s_1287_){
_start:
{
lean_object* v_iniSz_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; 
v_iniSz_1288_ = l_Lean_Parser_ParserState_stackSize(v_s_1287_);
v___x_1289_ = 1;
v___x_1290_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1284_, v_sep_1285_, v_allowTrailingSep_1283_, v_iniSz_1288_, v___x_1289_, v_c_1286_, v_s_1287_);
lean_dec(v_iniSz_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1291_, lean_object* v_p_1292_, lean_object* v_sep_1293_, lean_object* v_c_1294_, lean_object* v_s_1295_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1296_; lean_object* v_res_1297_; 
v_allowTrailingSep_boxed_1296_ = lean_unbox(v_allowTrailingSep_1291_);
v_res_1297_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1296_, v_p_1292_, v_sep_1293_, v_c_1294_, v_s_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1298_, lean_object* v_p_1299_, lean_object* v_sep_1300_, lean_object* v_c_1301_, lean_object* v_s_1302_){
_start:
{
lean_object* v_iniSz_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; 
v_iniSz_1303_ = l_Lean_Parser_ParserState_stackSize(v_s_1302_);
v___x_1304_ = 0;
v___x_1305_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1299_, v_sep_1300_, v_allowTrailingSep_1298_, v_iniSz_1303_, v___x_1304_, v_c_1301_, v_s_1302_);
lean_dec(v_iniSz_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1306_, lean_object* v_p_1307_, lean_object* v_sep_1308_, lean_object* v_c_1309_, lean_object* v_s_1310_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1311_; lean_object* v_res_1312_; 
v_allowTrailingSep_boxed_1311_ = lean_unbox(v_allowTrailingSep_1306_);
v_res_1312_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1311_, v_p_1307_, v_sep_1308_, v_c_1309_, v_s_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1313_, lean_object* v_sep_1314_){
_start:
{
lean_object* v_collectTokens_1315_; lean_object* v_collectKinds_1316_; lean_object* v_collectTokens_1317_; lean_object* v_collectKinds_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1328_; 
v_collectTokens_1315_ = lean_ctor_get(v_p_1313_, 0);
lean_inc_ref(v_collectTokens_1315_);
v_collectKinds_1316_ = lean_ctor_get(v_p_1313_, 1);
lean_inc_ref(v_collectKinds_1316_);
lean_dec_ref(v_p_1313_);
v_collectTokens_1317_ = lean_ctor_get(v_sep_1314_, 0);
v_collectKinds_1318_ = lean_ctor_get(v_sep_1314_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_sep_1314_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v_sep_1314_, 2);
lean_dec(v_unused_1329_);
v___x_1320_ = v_sep_1314_;
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_collectKinds_1318_);
lean_inc(v_collectTokens_1317_);
lean_dec(v_sep_1314_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1322_, 0, v_collectKinds_1318_);
lean_closure_set(v___f_1322_, 1, v_collectKinds_1316_);
v___f_1323_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1323_, 0, v_collectTokens_1317_);
lean_closure_set(v___f_1323_, 1, v_collectTokens_1315_);
v___x_1324_ = lean_box(1);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 2, v___x_1324_);
lean_ctor_set(v___x_1320_, 1, v___f_1322_);
lean_ctor_set(v___x_1320_, 0, v___f_1323_);
v___x_1326_ = v___x_1320_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___f_1323_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v___f_1322_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1330_, lean_object* v_sep_1331_){
_start:
{
lean_object* v_collectTokens_1332_; lean_object* v_collectKinds_1333_; lean_object* v_firstTokens_1334_; lean_object* v_collectTokens_1335_; lean_object* v_collectKinds_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1345_; 
v_collectTokens_1332_ = lean_ctor_get(v_p_1330_, 0);
lean_inc_ref(v_collectTokens_1332_);
v_collectKinds_1333_ = lean_ctor_get(v_p_1330_, 1);
lean_inc_ref(v_collectKinds_1333_);
v_firstTokens_1334_ = lean_ctor_get(v_p_1330_, 2);
lean_inc(v_firstTokens_1334_);
lean_dec_ref(v_p_1330_);
v_collectTokens_1335_ = lean_ctor_get(v_sep_1331_, 0);
v_collectKinds_1336_ = lean_ctor_get(v_sep_1331_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_sep_1331_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_sep_1331_, 2);
lean_dec(v_unused_1346_);
v___x_1338_ = v_sep_1331_;
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_collectKinds_1336_);
lean_inc(v_collectTokens_1335_);
lean_dec(v_sep_1331_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___f_1340_; lean_object* v___f_1341_; lean_object* v___x_1343_; 
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1340_, 0, v_collectKinds_1336_);
lean_closure_set(v___f_1340_, 1, v_collectKinds_1333_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1341_, 0, v_collectTokens_1335_);
lean_closure_set(v___f_1341_, 1, v_collectTokens_1332_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 2, v_firstTokens_1334_);
lean_ctor_set(v___x_1338_, 1, v___f_1340_);
lean_ctor_set(v___x_1338_, 0, v___f_1341_);
v___x_1343_ = v___x_1338_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___f_1341_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___f_1340_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_firstTokens_1334_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1347_, lean_object* v_sep_1348_, uint8_t v_allowTrailingSep_1349_){
_start:
{
lean_object* v_info_1350_; lean_object* v_fn_1351_; lean_object* v_info_1352_; lean_object* v_fn_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1363_; 
v_info_1350_ = lean_ctor_get(v_p_1347_, 0);
lean_inc_ref(v_info_1350_);
v_fn_1351_ = lean_ctor_get(v_p_1347_, 1);
lean_inc_ref(v_fn_1351_);
lean_dec_ref(v_p_1347_);
v_info_1352_ = lean_ctor_get(v_sep_1348_, 0);
v_fn_1353_ = lean_ctor_get(v_sep_1348_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_sep_1348_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1355_ = v_sep_1348_;
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_fn_1353_);
lean_inc(v_info_1352_);
lean_dec(v_sep_1348_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1357_ = l_Lean_Parser_sepByInfo(v_info_1350_, v_info_1352_);
v___x_1358_ = lean_box(v_allowTrailingSep_1349_);
v___x_1359_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1359_, 0, v___x_1358_);
lean_closure_set(v___x_1359_, 1, v_fn_1351_);
lean_closure_set(v___x_1359_, 2, v_fn_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1359_);
lean_ctor_set(v___x_1355_, 0, v___x_1357_);
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1364_, lean_object* v_sep_1365_, lean_object* v_allowTrailingSep_1366_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1367_; lean_object* v_res_1368_; 
v_allowTrailingSep_boxed_1367_ = lean_unbox(v_allowTrailingSep_1366_);
v_res_1368_ = l_Lean_Parser_sepByNoAntiquot(v_p_1364_, v_sep_1365_, v_allowTrailingSep_boxed_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1369_, lean_object* v_sep_1370_, uint8_t v_allowTrailingSep_1371_){
_start:
{
lean_object* v_info_1372_; lean_object* v_fn_1373_; lean_object* v_info_1374_; lean_object* v_fn_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1385_; 
v_info_1372_ = lean_ctor_get(v_p_1369_, 0);
lean_inc_ref(v_info_1372_);
v_fn_1373_ = lean_ctor_get(v_p_1369_, 1);
lean_inc_ref(v_fn_1373_);
lean_dec_ref(v_p_1369_);
v_info_1374_ = lean_ctor_get(v_sep_1370_, 0);
v_fn_1375_ = lean_ctor_get(v_sep_1370_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_sep_1370_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1377_ = v_sep_1370_;
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_fn_1375_);
lean_inc(v_info_1374_);
lean_dec(v_sep_1370_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1379_ = l_Lean_Parser_sepBy1Info(v_info_1372_, v_info_1374_);
v___x_1380_ = lean_box(v_allowTrailingSep_1371_);
v___x_1381_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1381_, 0, v___x_1380_);
lean_closure_set(v___x_1381_, 1, v_fn_1373_);
lean_closure_set(v___x_1381_, 2, v_fn_1375_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1381_);
lean_ctor_set(v___x_1377_, 0, v___x_1379_);
v___x_1383_ = v___x_1377_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1386_, lean_object* v_sep_1387_, lean_object* v_allowTrailingSep_1388_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1389_; lean_object* v_res_1390_; 
v_allowTrailingSep_boxed_1389_ = lean_unbox(v_allowTrailingSep_1388_);
v_res_1390_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1386_, v_sep_1387_, v_allowTrailingSep_boxed_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1391_, lean_object* v_f_1392_, lean_object* v_c_1393_, lean_object* v_s_1394_){
_start:
{
lean_object* v_s_1395_; lean_object* v_stxStack_1396_; lean_object* v_errorMsg_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_s_1395_ = lean_apply_2(v_p_1391_, v_c_1393_, v_s_1394_);
v_stxStack_1396_ = lean_ctor_get(v_s_1395_, 0);
lean_inc_ref(v_stxStack_1396_);
v_errorMsg_1397_ = lean_ctor_get(v_s_1395_, 4);
lean_inc(v_errorMsg_1397_);
v___x_1398_ = lean_box(0);
v___x_1399_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_dec_ref(v_stxStack_1396_);
lean_dec_ref(v_f_1392_);
return v_s_1395_;
}
else
{
lean_object* v_stx_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_stx_1400_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1396_);
lean_dec_ref(v_stxStack_1396_);
v___x_1401_ = l_Lean_Parser_ParserState_popSyntax(v_s_1395_);
v___x_1402_ = lean_apply_1(v_f_1392_, v_stx_1400_);
v___x_1403_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1401_, v___x_1402_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1404_){
_start:
{
lean_object* v_collectTokens_1405_; lean_object* v_collectKinds_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_collectTokens_1405_ = lean_ctor_get(v_p_1404_, 0);
v_collectKinds_1406_ = lean_ctor_get(v_p_1404_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_p_1404_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_p_1404_, 2);
lean_dec(v_unused_1415_);
v___x_1408_ = v_p_1404_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_collectKinds_1406_);
lean_inc(v_collectTokens_1405_);
lean_dec(v_p_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_box(1);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 2, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_collectTokens_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_collectKinds_1406_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1416_, lean_object* v_f_1417_){
_start:
{
lean_object* v_info_1418_; lean_object* v_fn_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1428_; 
v_info_1418_ = lean_ctor_get(v_p_1416_, 0);
v_fn_1419_ = lean_ctor_get(v_p_1416_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_p_1416_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1421_ = v_p_1416_;
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_fn_1419_);
lean_inc(v_info_1418_);
lean_dec(v_p_1416_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = l_Lean_Parser_withResultOfInfo(v_info_1418_);
v___x_1424_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1424_, 0, v_fn_1419_);
lean_closure_set(v___x_1424_, 1, v_f_1417_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v___x_1424_);
lean_ctor_set(v___x_1421_, 0, v___x_1423_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = l_Lean_Syntax_getNumArgs(v_stx_1429_);
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_dec_eq(v___x_1430_, v___x_1431_);
lean_dec(v___x_1430_);
if (v___x_1432_ == 0)
{
lean_inc(v_stx_1429_);
return v_stx_1429_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = l_Lean_Syntax_getArg(v_stx_1429_, v___x_1433_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1435_);
lean_dec(v_stx_1435_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1438_){
_start:
{
lean_object* v___f_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___f_1439_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1440_ = l_Lean_Parser_many1NoAntiquot(v_p_1438_);
v___x_1441_ = l_Lean_Parser_withResultOf(v___x_1440_, v___f_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1442_, lean_object* v_errorMsg_1443_, lean_object* v_c_1444_, lean_object* v_s_1445_){
_start:
{
lean_object* v_pos_1446_; lean_object* v_toInputContext_1447_; uint8_t v___x_1448_; 
v_pos_1446_ = lean_ctor_get(v_s_1445_, 2);
v_toInputContext_1447_ = lean_ctor_get(v_c_1444_, 0);
v___x_1448_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1447_, v_pos_1446_);
if (v___x_1448_ == 0)
{
lean_object* v_inputString_1449_; uint32_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_inputString_1449_ = lean_ctor_get(v_toInputContext_1447_, 0);
v___x_1450_ = lean_string_utf8_get_fast(v_inputString_1449_, v_pos_1446_);
v___x_1451_ = lean_box_uint32(v___x_1450_);
v___x_1452_ = lean_apply_1(v_p_1442_, v___x_1451_);
v___x_1453_ = lean_unbox(v___x_1452_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = 1;
v___x_1455_ = lean_box(0);
v___x_1456_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1445_, v_errorMsg_1443_, v___x_1455_, v___x_1454_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
lean_inc(v_pos_1446_);
lean_dec_ref(v_errorMsg_1443_);
v___x_1457_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1445_, v_c_1444_, v_pos_1446_);
lean_dec(v_pos_1446_);
return v___x_1457_;
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_errorMsg_1443_);
lean_dec_ref(v_p_1442_);
v___x_1458_ = lean_box(0);
v___x_1459_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1445_, v___x_1458_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1460_, lean_object* v_errorMsg_1461_, lean_object* v_c_1462_, lean_object* v_s_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Parser_satisfyFn(v_p_1460_, v_errorMsg_1461_, v_c_1462_, v_s_1463_);
lean_dec_ref(v_c_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1465_, lean_object* v_c_1466_, lean_object* v_s_1467_){
_start:
{
lean_object* v_pos_1468_; lean_object* v_toInputContext_1469_; uint8_t v___x_1470_; 
v_pos_1468_ = lean_ctor_get(v_s_1467_, 2);
v_toInputContext_1469_ = lean_ctor_get(v_c_1466_, 0);
v___x_1470_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1469_, v_pos_1468_);
if (v___x_1470_ == 0)
{
lean_object* v_inputString_1471_; uint32_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v_inputString_1471_ = lean_ctor_get(v_toInputContext_1469_, 0);
v___x_1472_ = lean_string_utf8_get_fast(v_inputString_1471_, v_pos_1468_);
v___x_1473_ = lean_box_uint32(v___x_1472_);
lean_inc_ref(v_p_1465_);
v___x_1474_ = lean_apply_1(v_p_1465_, v___x_1473_);
v___x_1475_ = lean_unbox(v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_inc(v_pos_1468_);
v___x_1476_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1467_, v_c_1466_, v_pos_1468_);
lean_dec(v_pos_1468_);
v_s_1467_ = v___x_1476_;
goto _start;
}
else
{
lean_dec_ref(v_p_1465_);
return v_s_1467_;
}
}
else
{
lean_dec_ref(v_p_1465_);
return v_s_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1478_, lean_object* v_c_1479_, lean_object* v_s_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Parser_takeUntilFn(v_p_1478_, v_c_1479_, v_s_1480_);
lean_dec_ref(v_c_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1482_, uint32_t v_c_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_box_uint32(v_c_1483_);
v___x_1485_ = lean_apply_1(v_p_1482_, v___x_1484_);
v___x_1486_ = lean_unbox(v___x_1485_);
if (v___x_1486_ == 0)
{
uint8_t v___x_1487_; 
v___x_1487_ = 1;
return v___x_1487_;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = 0;
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1489_, lean_object* v_c_1490_){
_start:
{
uint32_t v_c_boxed_1491_; uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_c_boxed_1491_ = lean_unbox_uint32(v_c_1490_);
lean_dec(v_c_1490_);
v_res_1492_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1489_, v_c_boxed_1491_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___f_1497_; lean_object* v___x_1498_; 
v___f_1497_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1497_, 0, v_p_1494_);
v___x_1498_ = l_Lean_Parser_takeUntilFn(v___f_1497_, v_a_1495_, v_a_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Parser_takeWhileFn(v_p_1499_, v_a_1500_, v_a_1501_);
lean_dec_ref(v_a_1500_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1503_, lean_object* v_errorMsg_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_inc_ref(v_p_1503_);
v___x_1507_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1507_, 0, v_p_1503_);
lean_closure_set(v___x_1507_, 1, v_errorMsg_1504_);
v___x_1508_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1508_, 0, v_p_1503_);
v___x_1509_ = l_Lean_Parser_andthenFn(v___x_1507_, v___x_1508_, v_a_1505_, v_a_1506_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1511_, lean_object* v_s_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1514_ = lean_box(0);
v___x_1515_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1512_, v___x_1513_, v___x_1514_, v_pushMissingOnError_1511_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1516_, lean_object* v_s_1517_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1518_; lean_object* v_res_1519_; 
v_pushMissingOnError_boxed_1518_ = lean_unbox(v_pushMissingOnError_1516_);
v_res_1519_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1518_, v_s_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1520_, lean_object* v_nesting_1521_, lean_object* v_c_1522_, lean_object* v_s_1523_){
_start:
{
lean_object* v_pos_1524_; lean_object* v_toInputContext_1525_; uint8_t v___x_1526_; 
v_pos_1524_ = lean_ctor_get(v_s_1523_, 2);
v_toInputContext_1525_ = lean_ctor_get(v_c_1522_, 0);
v___x_1526_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1525_, v_pos_1524_);
if (v___x_1526_ == 0)
{
lean_object* v_inputString_1527_; uint32_t v_curr_1528_; lean_object* v_i_1529_; uint32_t v___x_1530_; uint8_t v___x_1531_; 
v_inputString_1527_ = lean_ctor_get(v_toInputContext_1525_, 0);
v_curr_1528_ = lean_string_utf8_get_fast(v_inputString_1527_, v_pos_1524_);
v_i_1529_ = lean_string_utf8_next_fast(v_inputString_1527_, v_pos_1524_);
v___x_1530_ = 45;
v___x_1531_ = lean_uint32_dec_eq(v_curr_1528_, v___x_1530_);
if (v___x_1531_ == 0)
{
uint32_t v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = 47;
v___x_1533_ = lean_uint32_dec_eq(v_curr_1528_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Parser_ParserState_setPos(v_s_1523_, v_i_1529_);
v_s_1523_ = v___x_1534_;
goto _start;
}
else
{
uint8_t v___x_1536_; 
v___x_1536_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1525_, v_i_1529_);
if (v___x_1536_ == 0)
{
uint32_t v_curr_1537_; uint8_t v___x_1538_; 
v_curr_1537_ = lean_string_utf8_get_fast(v_inputString_1527_, v_i_1529_);
v___x_1538_ = lean_uint32_dec_eq(v_curr_1537_, v___x_1530_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Parser_ParserState_setPos(v_s_1523_, v_i_1529_);
v_s_1523_ = v___x_1539_;
goto _start;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_add(v_nesting_1521_, v___x_1541_);
lean_dec(v_nesting_1521_);
v___x_1543_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1523_, v_c_1522_, v_i_1529_);
v_nesting_1521_ = v___x_1542_;
v_s_1523_ = v___x_1543_;
goto _start;
}
}
else
{
lean_object* v___x_1545_; 
lean_dec(v_nesting_1521_);
v___x_1545_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1520_, v_s_1523_);
return v___x_1545_;
}
}
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1525_, v_i_1529_);
if (v___x_1546_ == 0)
{
uint32_t v_curr_1547_; uint32_t v___x_1548_; uint8_t v___x_1549_; 
v_curr_1547_ = lean_string_utf8_get_fast(v_inputString_1527_, v_i_1529_);
v___x_1548_ = 47;
v___x_1549_ = lean_uint32_dec_eq(v_curr_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Parser_ParserState_setPos(v_s_1523_, v_i_1529_);
v_s_1523_ = v___x_1550_;
goto _start;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_dec_eq(v_nesting_1521_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_nat_sub(v_nesting_1521_, v___x_1552_);
lean_dec(v_nesting_1521_);
v___x_1555_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1523_, v_c_1522_, v_i_1529_);
v_nesting_1521_ = v___x_1554_;
v_s_1523_ = v___x_1555_;
goto _start;
}
else
{
lean_object* v___x_1557_; 
lean_dec(v_nesting_1521_);
v___x_1557_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1523_, v_c_1522_, v_i_1529_);
return v___x_1557_;
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec(v_nesting_1521_);
v___x_1558_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1520_, v_s_1523_);
return v___x_1558_;
}
}
}
else
{
lean_object* v___x_1559_; 
lean_dec(v_nesting_1521_);
v___x_1559_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1520_, v_s_1523_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1560_, lean_object* v_nesting_1561_, lean_object* v_c_1562_, lean_object* v_s_1563_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1564_; lean_object* v_res_1565_; 
v_pushMissingOnError_boxed_1564_ = lean_unbox(v_pushMissingOnError_1560_);
v_res_1565_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1564_, v_nesting_1561_, v_c_1562_, v_s_1563_);
lean_dec_ref(v_c_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1566_){
_start:
{
uint32_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = 10;
v___x_1568_ = lean_uint32_dec_eq(v_c_1566_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1569_){
_start:
{
uint32_t v_c_boxed_1570_; uint8_t v_res_1571_; lean_object* v_r_1572_; 
v_c_boxed_1570_ = lean_unbox_uint32(v_c_1569_);
lean_dec(v_c_1569_);
v_res_1571_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1570_);
v_r_1572_ = lean_box(v_res_1571_);
return v_r_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1578_, lean_object* v_s_1579_){
_start:
{
lean_object* v_pos_1580_; lean_object* v_toInputContext_1584_; uint8_t v___x_1585_; 
v_pos_1580_ = lean_ctor_get(v_s_1579_, 2);
v_toInputContext_1584_ = lean_ctor_get(v_c_1578_, 0);
v___x_1585_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1584_, v_pos_1580_);
if (v___x_1585_ == 0)
{
lean_object* v_inputString_1586_; uint32_t v_curr_1587_; uint32_t v___x_1588_; uint8_t v___x_1589_; 
v_inputString_1586_ = lean_ctor_get(v_toInputContext_1584_, 0);
v_curr_1587_ = lean_string_utf8_get_fast(v_inputString_1586_, v_pos_1580_);
v___x_1588_ = 9;
v___x_1589_ = lean_uint32_dec_eq(v_curr_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
uint32_t v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = 13;
v___x_1591_ = lean_uint32_dec_eq(v_curr_1587_, v___x_1590_);
if (v___x_1591_ == 0)
{
uint8_t v___y_1593_; uint8_t v___y_1620_; uint32_t v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = 32;
v___x_1624_ = lean_uint32_dec_eq(v_curr_1587_, v___x_1623_);
if (v___x_1624_ == 0)
{
v___y_1620_ = v___x_1589_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___x_1624_;
goto v___jp_1619_;
}
v___jp_1592_:
{
if (v___y_1593_ == 0)
{
uint32_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = 45;
v___x_1595_ = lean_uint32_dec_eq(v_curr_1587_, v___x_1594_);
if (v___x_1595_ == 0)
{
uint32_t v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = 47;
v___x_1597_ = lean_uint32_dec_eq(v_curr_1587_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v_c_1578_);
return v_s_1579_;
}
else
{
lean_object* v_i_1598_; uint32_t v_curr_1599_; uint8_t v___x_1600_; 
v_i_1598_ = lean_string_utf8_next_fast(v_inputString_1586_, v_pos_1580_);
v_curr_1599_ = lean_string_utf8_get(v_inputString_1586_, v_i_1598_);
v___x_1600_ = lean_uint32_dec_eq(v_curr_1599_, v___x_1594_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v_c_1578_);
return v_s_1579_;
}
else
{
lean_object* v_i_1601_; uint32_t v_curr_1602_; uint8_t v___x_1603_; 
v_i_1601_ = lean_string_utf8_next(v_inputString_1586_, v_i_1598_);
v_curr_1602_ = lean_string_utf8_get(v_inputString_1586_, v_i_1601_);
v___x_1603_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1594_);
if (v___x_1603_ == 0)
{
uint32_t v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = 33;
v___x_1605_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_box(v___x_1605_);
v___x_1608_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1608_, 0, v___x_1607_);
lean_closure_set(v___x_1608_, 1, v___x_1606_);
v___x_1609_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1610_ = l_Lean_Parser_ParserState_next(v_s_1579_, v_c_1578_, v_i_1601_);
lean_dec(v_i_1601_);
v___x_1611_ = l_Lean_Parser_andthenFn(v___x_1608_, v___x_1609_, v_c_1578_, v___x_1610_);
return v___x_1611_;
}
else
{
lean_dec(v_i_1601_);
lean_dec_ref(v_c_1578_);
return v_s_1579_;
}
}
else
{
lean_dec(v_i_1601_);
lean_dec_ref(v_c_1578_);
return v_s_1579_;
}
}
}
}
else
{
lean_object* v_i_1612_; uint32_t v_curr_1613_; uint8_t v___x_1614_; 
v_i_1612_ = lean_string_utf8_next_fast(v_inputString_1586_, v_pos_1580_);
v_curr_1613_ = lean_string_utf8_get(v_inputString_1586_, v_i_1612_);
v___x_1614_ = lean_uint32_dec_eq(v_curr_1613_, v___x_1594_);
if (v___x_1614_ == 0)
{
lean_dec_ref(v_c_1578_);
return v_s_1579_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1615_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1616_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1617_ = l_Lean_Parser_ParserState_next(v_s_1579_, v_c_1578_, v_i_1612_);
v___x_1618_ = l_Lean_Parser_andthenFn(v___x_1615_, v___x_1616_, v_c_1578_, v___x_1617_);
return v___x_1618_;
}
}
}
else
{
lean_inc(v_pos_1580_);
goto v___jp_1581_;
}
}
v___jp_1619_:
{
if (v___y_1620_ == 0)
{
if (v___x_1591_ == 0)
{
uint32_t v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = 10;
v___x_1622_ = lean_uint32_dec_eq(v_curr_1587_, v___x_1621_);
v___y_1593_ = v___x_1622_;
goto v___jp_1592_;
}
else
{
v___y_1593_ = v___x_1591_;
goto v___jp_1592_;
}
}
else
{
lean_inc(v_pos_1580_);
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v_c_1578_);
v___x_1625_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1626_ = lean_box(0);
v___x_1627_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1579_, v___x_1625_, v___x_1626_, v___x_1589_);
return v___x_1627_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec_ref(v_c_1578_);
v___x_1628_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1629_ = lean_box(0);
v___x_1630_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1579_, v___x_1628_, v___x_1629_, v___x_1585_);
return v___x_1630_;
}
}
else
{
lean_dec_ref(v_c_1578_);
return v_s_1579_;
}
v___jp_1581_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1579_, v_c_1578_, v_pos_1580_);
lean_dec(v_pos_1580_);
v_s_1579_ = v___x_1582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1631_, lean_object* v_p_1632_){
_start:
{
lean_object* v_toInputContext_1633_; lean_object* v_inputString_1634_; lean_object* v_endPos_1635_; uint8_t v___x_1636_; 
v_toInputContext_1633_ = lean_ctor_get(v_c_1631_, 0);
v_inputString_1634_ = lean_ctor_get(v_toInputContext_1633_, 0);
v_endPos_1635_ = lean_ctor_get(v_toInputContext_1633_, 3);
v___x_1636_ = lean_nat_dec_le(v_p_1632_, v_endPos_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_inc(v_endPos_1635_);
lean_inc_ref(v_inputString_1634_);
v___x_1637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1637_, 0, v_inputString_1634_);
lean_ctor_set(v___x_1637_, 1, v_p_1632_);
lean_ctor_set(v___x_1637_, 2, v_endPos_1635_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; 
lean_inc(v_p_1632_);
lean_inc_ref(v_inputString_1634_);
v___x_1638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1638_, 0, v_inputString_1634_);
lean_ctor_set(v___x_1638_, 1, v_p_1632_);
lean_ctor_set(v___x_1638_, 2, v_p_1632_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1639_, lean_object* v_p_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1639_, v_p_1640_);
lean_dec_ref(v_c_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1642_, uint8_t v_trailingWs_1643_, lean_object* v_c_1644_, lean_object* v_s_1645_){
_start:
{
lean_object* v_toInputContext_1646_; lean_object* v_pos_1647_; lean_object* v_inputString_1648_; lean_object* v_endPos_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1677_; 
v_toInputContext_1646_ = lean_ctor_get(v_c_1644_, 0);
lean_inc_ref(v_toInputContext_1646_);
v_pos_1647_ = lean_ctor_get(v_s_1645_, 2);
v_inputString_1648_ = lean_ctor_get(v_toInputContext_1646_, 0);
v_endPos_1649_ = lean_ctor_get(v_toInputContext_1646_, 3);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_toInputContext_1646_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; 
v_unused_1678_ = lean_ctor_get(v_toInputContext_1646_, 2);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_toInputContext_1646_, 1);
lean_dec(v_unused_1679_);
v___x_1651_ = v_toInputContext_1646_;
v_isShared_1652_ = v_isSharedCheck_1677_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_endPos_1649_);
lean_inc(v_inputString_1648_);
lean_dec(v_toInputContext_1646_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1677_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v_leading_1653_; lean_object* v_val_1654_; 
lean_inc(v_startPos_1642_);
v_leading_1653_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1644_, v_startPos_1642_);
v_val_1654_ = lean_string_utf8_extract(v_inputString_1648_, v_startPos_1642_, v_pos_1647_);
if (v_trailingWs_1643_ == 0)
{
lean_object* v_trailing_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_dec(v_endPos_1649_);
lean_dec_ref(v_inputString_1648_);
lean_inc(v_pos_1647_);
v_trailing_1655_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1644_, v_pos_1647_);
lean_dec_ref(v_c_1644_);
v___x_1656_ = lean_string_utf8_byte_size(v_val_1654_);
v___x_1657_ = lean_nat_add(v_startPos_1642_, v___x_1656_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 3, v___x_1657_);
lean_ctor_set(v___x_1651_, 2, v_trailing_1655_);
lean_ctor_set(v___x_1651_, 1, v_startPos_1642_);
lean_ctor_set(v___x_1651_, 0, v_leading_1653_);
v___x_1659_ = v___x_1651_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_leading_1653_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_startPos_1642_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_trailing_1655_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v_atom_1660_; lean_object* v___x_1661_; 
v_atom_1660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1660_, 0, v___x_1659_);
lean_ctor_set(v_atom_1660_, 1, v_val_1654_);
v___x_1661_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1645_, v_atom_1660_);
return v___x_1661_;
}
}
else
{
lean_object* v_s_1663_; lean_object* v___y_1665_; lean_object* v_pos_1673_; uint8_t v___x_1674_; 
lean_inc(v_pos_1647_);
v_s_1663_ = l_Lean_Parser_whitespace(v_c_1644_, v_s_1645_);
v_pos_1673_ = lean_ctor_get(v_s_1663_, 2);
lean_inc(v_pos_1673_);
v___x_1674_ = lean_nat_dec_le(v_pos_1673_, v_endPos_1649_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
lean_dec(v_pos_1673_);
v___x_1675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1675_, 0, v_inputString_1648_);
lean_ctor_set(v___x_1675_, 1, v_pos_1647_);
lean_ctor_set(v___x_1675_, 2, v_endPos_1649_);
v___y_1665_ = v___x_1675_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_endPos_1649_);
v___x_1676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1676_, 0, v_inputString_1648_);
lean_ctor_set(v___x_1676_, 1, v_pos_1647_);
lean_ctor_set(v___x_1676_, 2, v_pos_1673_);
v___y_1665_ = v___x_1676_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_string_utf8_byte_size(v_val_1654_);
v___x_1667_ = lean_nat_add(v_startPos_1642_, v___x_1666_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 3, v___x_1667_);
lean_ctor_set(v___x_1651_, 2, v___y_1665_);
lean_ctor_set(v___x_1651_, 1, v_startPos_1642_);
lean_ctor_set(v___x_1651_, 0, v_leading_1653_);
v___x_1669_ = v___x_1651_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_leading_1653_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_startPos_1642_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v___y_1665_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v_atom_1670_; lean_object* v___x_1671_; 
v_atom_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1670_, 0, v___x_1669_);
lean_ctor_set(v_atom_1670_, 1, v_val_1654_);
v___x_1671_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1663_, v_atom_1670_);
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1680_, lean_object* v_trailingWs_1681_, lean_object* v_c_1682_, lean_object* v_s_1683_){
_start:
{
uint8_t v_trailingWs_boxed_1684_; lean_object* v_res_1685_; 
v_trailingWs_boxed_1684_ = lean_unbox(v_trailingWs_1681_);
v_res_1685_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1680_, v_trailingWs_boxed_1684_, v_c_1682_, v_s_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1686_, uint8_t v_trailingWs_1687_, lean_object* v_c_1688_, lean_object* v_s_1689_){
_start:
{
lean_object* v_pos_1690_; lean_object* v_s_1691_; lean_object* v_errorMsg_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_pos_1690_ = lean_ctor_get(v_s_1689_, 2);
lean_inc(v_pos_1690_);
lean_inc_ref(v_c_1688_);
v_s_1691_ = lean_apply_2(v_p_1686_, v_c_1688_, v_s_1689_);
v_errorMsg_1692_ = lean_ctor_get(v_s_1691_, 4);
lean_inc(v_errorMsg_1692_);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1692_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_dec(v_pos_1690_);
lean_dec_ref(v_c_1688_);
return v_s_1691_;
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1690_, v_trailingWs_1687_, v_c_1688_, v_s_1691_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1696_, lean_object* v_trailingWs_1697_, lean_object* v_c_1698_, lean_object* v_s_1699_){
_start:
{
uint8_t v_trailingWs_boxed_1700_; lean_object* v_res_1701_; 
v_trailingWs_boxed_1700_ = lean_unbox(v_trailingWs_1697_);
v_res_1701_ = l_Lean_Parser_rawFn(v_p_1696_, v_trailingWs_boxed_1700_, v_c_1698_, v_s_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1702_, uint32_t v_d_1703_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_uint32_dec_eq(v_c_1702_, v_d_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1705_, lean_object* v_d_1706_){
_start:
{
uint32_t v_c_boxed_1707_; uint32_t v_d_boxed_1708_; uint8_t v_res_1709_; lean_object* v_r_1710_; 
v_c_boxed_1707_ = lean_unbox_uint32(v_c_1705_);
lean_dec(v_c_1705_);
v_d_boxed_1708_ = lean_unbox_uint32(v_d_1706_);
lean_dec(v_d_1706_);
v_res_1709_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1707_, v_d_boxed_1708_);
v_r_1710_ = lean_box(v_res_1709_);
return v_r_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1713_, uint8_t v_trailingWs_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1717_ = lean_box_uint32(v_c_1713_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1718_, 0, v___x_1717_);
v___x_1719_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1720_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1721_ = lean_string_push(v___x_1720_, v_c_1713_);
v___x_1722_ = lean_string_append(v___x_1719_, v___x_1721_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = lean_string_append(v___x_1722_, v___x_1719_);
v___x_1724_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1724_, 0, v___f_1718_);
lean_closure_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = l_Lean_Parser_rawFn(v___x_1724_, v_trailingWs_1714_, v_a_1715_, v_a_1716_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1726_, lean_object* v_trailingWs_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
uint32_t v_c_boxed_1730_; uint8_t v_trailingWs_boxed_1731_; lean_object* v_res_1732_; 
v_c_boxed_1730_ = lean_unbox_uint32(v_c_1726_);
lean_dec(v_c_1726_);
v_trailingWs_boxed_1731_ = lean_unbox(v_trailingWs_1727_);
v_res_1732_ = l_Lean_Parser_chFn(v_c_boxed_1730_, v_trailingWs_boxed_1731_, v_a_1728_, v_a_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1733_, uint8_t v_trailingWs_1734_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1735_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1736_ = lean_box_uint32(v_c_1733_);
v___x_1737_ = lean_box(v_trailingWs_1734_);
v___x_1738_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1738_, 0, v___x_1736_);
lean_closure_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1735_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1740_, lean_object* v_trailingWs_1741_){
_start:
{
uint32_t v_c_boxed_1742_; uint8_t v_trailingWs_boxed_1743_; lean_object* v_res_1744_; 
v_c_boxed_1742_ = lean_unbox_uint32(v_c_1740_);
lean_dec(v_c_1740_);
v_trailingWs_boxed_1743_ = lean_unbox(v_trailingWs_1741_);
v_res_1744_ = l_Lean_Parser_rawCh(v_c_boxed_1742_, v_trailingWs_boxed_1743_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1746_, lean_object* v_s_1747_){
_start:
{
lean_object* v_pos_1748_; lean_object* v_toInputContext_1749_; uint8_t v___x_1750_; 
v_pos_1748_ = lean_ctor_get(v_s_1747_, 2);
v_toInputContext_1749_ = lean_ctor_get(v_c_1746_, 0);
v___x_1750_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1749_, v_pos_1748_);
if (v___x_1750_ == 0)
{
lean_object* v_inputString_1751_; uint8_t v___x_1752_; uint32_t v_curr_1753_; lean_object* v_i_1754_; uint8_t v___y_1756_; uint8_t v___y_1762_; uint8_t v___y_1769_; uint32_t v___x_1775_; uint8_t v___x_1776_; 
v_inputString_1751_ = lean_ctor_get(v_toInputContext_1749_, 0);
v___x_1752_ = 1;
v_curr_1753_ = lean_string_utf8_get_fast(v_inputString_1751_, v_pos_1748_);
v_i_1754_ = lean_string_utf8_next_fast(v_inputString_1751_, v_pos_1748_);
v___x_1775_ = 48;
v___x_1776_ = lean_uint32_dec_le(v___x_1775_, v_curr_1753_);
if (v___x_1776_ == 0)
{
v___y_1769_ = v___x_1776_;
goto v___jp_1768_;
}
else
{
uint32_t v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = 57;
v___x_1778_ = lean_uint32_dec_le(v_curr_1753_, v___x_1777_);
v___y_1769_ = v___x_1778_;
goto v___jp_1768_;
}
v___jp_1755_:
{
if (v___y_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1747_, v___x_1757_, v___x_1758_, v___x_1752_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Parser_ParserState_setPos(v_s_1747_, v_i_1754_);
return v___x_1760_;
}
}
v___jp_1761_:
{
if (v___y_1762_ == 0)
{
uint32_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = 65;
v___x_1764_ = lean_uint32_dec_le(v___x_1763_, v_curr_1753_);
if (v___x_1764_ == 0)
{
v___y_1756_ = v___x_1764_;
goto v___jp_1755_;
}
else
{
uint32_t v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = 70;
v___x_1766_ = lean_uint32_dec_le(v_curr_1753_, v___x_1765_);
v___y_1756_ = v___x_1766_;
goto v___jp_1755_;
}
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Parser_ParserState_setPos(v_s_1747_, v_i_1754_);
return v___x_1767_;
}
}
v___jp_1768_:
{
if (v___y_1769_ == 0)
{
uint32_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = 97;
v___x_1771_ = lean_uint32_dec_le(v___x_1770_, v_curr_1753_);
if (v___x_1771_ == 0)
{
v___y_1762_ = v___x_1771_;
goto v___jp_1761_;
}
else
{
uint32_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = 102;
v___x_1773_ = lean_uint32_dec_le(v_curr_1753_, v___x_1772_);
v___y_1762_ = v___x_1773_;
goto v___jp_1761_;
}
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Parser_ParserState_setPos(v_s_1747_, v_i_1754_);
return v___x_1774_;
}
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_box(0);
v___x_1780_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1747_, v___x_1779_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1781_, lean_object* v_s_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Parser_hexDigitFn(v_c_1781_, v_s_1782_);
lean_dec_ref(v_c_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1786_, lean_object* v_c_1787_, lean_object* v_s_1788_){
_start:
{
lean_object* v_pos_1789_; lean_object* v_toInputContext_1793_; uint8_t v___x_1794_; 
v_pos_1789_ = lean_ctor_get(v_s_1788_, 2);
v_toInputContext_1793_ = lean_ctor_get(v_c_1787_, 0);
v___x_1794_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1793_, v_pos_1789_);
if (v___x_1794_ == 0)
{
lean_object* v_inputString_1795_; uint8_t v___x_1796_; uint8_t v___y_1798_; uint32_t v_curr_1802_; uint8_t v___y_1804_; uint32_t v___x_1809_; uint8_t v___x_1810_; 
v_inputString_1795_ = lean_ctor_get(v_toInputContext_1793_, 0);
v___x_1796_ = 1;
v_curr_1802_ = lean_string_utf8_get_fast(v_inputString_1795_, v_pos_1789_);
v___x_1809_ = 10;
v___x_1810_ = lean_uint32_dec_eq(v_curr_1802_, v___x_1809_);
if (v___x_1810_ == 0)
{
uint32_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = 32;
v___x_1812_ = lean_uint32_dec_eq(v_curr_1802_, v___x_1811_);
if (v___x_1812_ == 0)
{
uint32_t v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = 9;
v___x_1814_ = lean_uint32_dec_eq(v_curr_1802_, v___x_1813_);
v___y_1804_ = v___x_1814_;
goto v___jp_1803_;
}
else
{
v___y_1804_ = v___x_1812_;
goto v___jp_1803_;
}
}
else
{
if (v_seenNewline_1786_ == 0)
{
lean_object* v___x_1815_; 
lean_inc(v_pos_1789_);
v___x_1815_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1788_, v_c_1787_, v_pos_1789_);
lean_dec(v_pos_1789_);
v_seenNewline_1786_ = v___x_1796_;
v_s_1788_ = v___x_1815_;
goto _start;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1818_ = lean_box(0);
v___x_1819_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1788_, v___x_1817_, v___x_1818_, v___x_1796_);
return v___x_1819_;
}
}
v___jp_1797_:
{
if (v___y_1798_ == 0)
{
if (v_seenNewline_1786_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1800_ = lean_box(0);
v___x_1801_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1788_, v___x_1799_, v___x_1800_, v___x_1796_);
return v___x_1801_;
}
else
{
return v_s_1788_;
}
}
else
{
lean_inc(v_pos_1789_);
goto v___jp_1790_;
}
}
v___jp_1803_:
{
if (v___y_1804_ == 0)
{
uint32_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = 13;
v___x_1806_ = lean_uint32_dec_eq(v_curr_1802_, v___x_1805_);
if (v___x_1806_ == 0)
{
uint32_t v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = 10;
v___x_1808_ = lean_uint32_dec_eq(v_curr_1802_, v___x_1807_);
v___y_1798_ = v___x_1808_;
goto v___jp_1797_;
}
else
{
v___y_1798_ = v___x_1806_;
goto v___jp_1797_;
}
}
else
{
lean_inc(v_pos_1789_);
goto v___jp_1790_;
}
}
}
else
{
return v_s_1788_;
}
v___jp_1790_:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1788_, v_c_1787_, v_pos_1789_);
lean_dec(v_pos_1789_);
v_s_1788_ = v___x_1791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1820_, lean_object* v_c_1821_, lean_object* v_s_1822_){
_start:
{
uint8_t v_seenNewline_boxed_1823_; lean_object* v_res_1824_; 
v_seenNewline_boxed_1823_ = lean_unbox(v_seenNewline_1820_);
v_res_1824_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1823_, v_c_1821_, v_s_1822_);
lean_dec_ref(v_c_1821_);
return v_res_1824_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1826_);
v___x_1827_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1827_, 0, v___x_1826_);
lean_closure_set(v___x_1827_, 1, v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1829_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1830_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1830_, 0, v___x_1829_);
lean_closure_set(v___x_1830_, 1, v___x_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1831_, uint8_t v_inString_1832_, lean_object* v_c_1833_, lean_object* v_s_1834_){
_start:
{
lean_object* v_pos_1835_; lean_object* v_toInputContext_1836_; uint8_t v___x_1837_; 
v_pos_1835_ = lean_ctor_get(v_s_1834_, 2);
v_toInputContext_1836_ = lean_ctor_get(v_c_1833_, 0);
v___x_1837_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1836_, v_pos_1835_);
if (v___x_1837_ == 0)
{
lean_object* v_inputString_1838_; uint32_t v_curr_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_inputString_1838_ = lean_ctor_get(v_toInputContext_1836_, 0);
v_curr_1839_ = lean_string_utf8_get_fast(v_inputString_1838_, v_pos_1835_);
v___x_1840_ = lean_box_uint32(v_curr_1839_);
v___x_1841_ = lean_apply_1(v_isQuotable_1831_, v___x_1840_);
v___x_1842_ = lean_unbox(v___x_1841_);
if (v___x_1842_ == 0)
{
uint32_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = 120;
v___x_1844_ = lean_uint32_dec_eq(v_curr_1839_, v___x_1843_);
if (v___x_1844_ == 0)
{
uint32_t v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = 117;
v___x_1846_ = lean_uint32_dec_eq(v_curr_1839_, v___x_1845_);
if (v___x_1846_ == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = 1;
if (v_inString_1832_ == 0)
{
lean_dec_ref(v_c_1833_);
goto v___jp_1848_;
}
else
{
uint32_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = 10;
v___x_1853_ = lean_uint32_dec_eq(v_curr_1839_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec_ref(v_c_1833_);
goto v___jp_1848_;
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Parser_stringGapFn(v___x_1846_, v_c_1833_, v_s_1834_);
lean_dec_ref(v_c_1833_);
return v___x_1854_;
}
}
v___jp_1848_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1834_, v___x_1849_, v___x_1850_, v___x_1847_);
return v___x_1851_;
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_inc(v_pos_1835_);
v___x_1855_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1856_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1857_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1834_, v_c_1833_, v_pos_1835_);
lean_dec(v_pos_1835_);
v___x_1858_ = l_Lean_Parser_andthenFn(v___x_1855_, v___x_1856_, v_c_1833_, v___x_1857_);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_inc(v_pos_1835_);
v___x_1859_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1860_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1834_, v_c_1833_, v_pos_1835_);
lean_dec(v_pos_1835_);
lean_inc_ref(v___x_1859_);
v___x_1861_ = l_Lean_Parser_andthenFn(v___x_1859_, v___x_1859_, v_c_1833_, v___x_1860_);
return v___x_1861_;
}
}
else
{
lean_object* v___x_1862_; 
lean_inc(v_pos_1835_);
v___x_1862_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1834_, v_c_1833_, v_pos_1835_);
lean_dec(v_pos_1835_);
lean_dec_ref(v_c_1833_);
return v___x_1862_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_c_1833_);
lean_dec_ref(v_isQuotable_1831_);
v___x_1863_ = lean_box(0);
v___x_1864_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1834_, v___x_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1865_, lean_object* v_inString_1866_, lean_object* v_c_1867_, lean_object* v_s_1868_){
_start:
{
uint8_t v_inString_boxed_1869_; lean_object* v_res_1870_; 
v_inString_boxed_1869_ = lean_unbox(v_inString_1866_);
v_res_1870_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1865_, v_inString_boxed_1869_, v_c_1867_, v_s_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1871_){
_start:
{
uint8_t v___y_1873_; uint32_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = 92;
v___x_1883_ = lean_uint32_dec_eq(v_c_1871_, v___x_1882_);
if (v___x_1883_ == 0)
{
uint32_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = 34;
v___x_1885_ = lean_uint32_dec_eq(v_c_1871_, v___x_1884_);
v___y_1873_ = v___x_1885_;
goto v___jp_1872_;
}
else
{
v___y_1873_ = v___x_1883_;
goto v___jp_1872_;
}
v___jp_1872_:
{
if (v___y_1873_ == 0)
{
uint32_t v___x_1874_; uint8_t v___x_1875_; 
v___x_1874_ = 39;
v___x_1875_ = lean_uint32_dec_eq(v_c_1871_, v___x_1874_);
if (v___x_1875_ == 0)
{
uint32_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = 114;
v___x_1877_ = lean_uint32_dec_eq(v_c_1871_, v___x_1876_);
if (v___x_1877_ == 0)
{
uint32_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = 110;
v___x_1879_ = lean_uint32_dec_eq(v_c_1871_, v___x_1878_);
if (v___x_1879_ == 0)
{
uint32_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = 116;
v___x_1881_ = lean_uint32_dec_eq(v_c_1871_, v___x_1880_);
return v___x_1881_;
}
else
{
return v___x_1879_;
}
}
else
{
return v___x_1877_;
}
}
else
{
return v___x_1875_;
}
}
else
{
return v___y_1873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1886_){
_start:
{
uint32_t v_c_boxed_1887_; uint8_t v_res_1888_; lean_object* v_r_1889_; 
v_c_boxed_1887_ = lean_unbox_uint32(v_c_1886_);
lean_dec(v_c_1886_);
v_res_1888_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1887_);
v_r_1889_ = lean_box(v_res_1888_);
return v_r_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1894_ = 0;
v___x_1895_ = l_Lean_Parser_quotedCharCoreFn(v___x_1893_, v___x_1894_, v_a_1891_, v_a_1892_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1899_ = 1;
v___x_1900_ = l_Lean_Parser_quotedCharCoreFn(v___x_1898_, v___x_1899_, v_a_1896_, v_a_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1901_, lean_object* v_startPos_1902_, uint8_t v_includeWhitespace_1903_, lean_object* v_c_1904_, lean_object* v_s_1905_){
_start:
{
lean_object* v_pos_1906_; lean_object* v_errorMsg_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v_pos_1906_ = lean_ctor_get(v_s_1905_, 2);
v_errorMsg_1907_ = lean_ctor_get(v_s_1905_, 4);
v___x_1908_ = lean_box(0);
lean_inc(v_errorMsg_1907_);
v___x_1909_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1907_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v_c_1904_);
lean_dec(v_startPos_1902_);
lean_dec(v_n_1901_);
return v_s_1905_;
}
else
{
lean_object* v_toInputContext_1910_; lean_object* v_inputString_1911_; lean_object* v_endPos_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1934_; 
lean_inc(v_pos_1906_);
v_toInputContext_1910_ = lean_ctor_get(v_c_1904_, 0);
lean_inc_ref(v_toInputContext_1910_);
v_inputString_1911_ = lean_ctor_get(v_toInputContext_1910_, 0);
v_endPos_1912_ = lean_ctor_get(v_toInputContext_1910_, 3);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_toInputContext_1910_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1935_ = lean_ctor_get(v_toInputContext_1910_, 2);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_toInputContext_1910_, 1);
lean_dec(v_unused_1936_);
v___x_1914_ = v_toInputContext_1910_;
v_isShared_1915_ = v_isSharedCheck_1934_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_endPos_1912_);
lean_inc(v_inputString_1911_);
lean_dec(v_toInputContext_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1934_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_leading_1916_; lean_object* v_val_1917_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1927_; lean_object* v_pos_1928_; 
lean_inc(v_startPos_1902_);
v_leading_1916_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1904_, v_startPos_1902_);
v_val_1917_ = lean_string_utf8_extract(v_inputString_1911_, v_startPos_1902_, v_pos_1906_);
if (v_includeWhitespace_1903_ == 0)
{
lean_dec_ref(v_c_1904_);
lean_inc(v_pos_1906_);
v___y_1927_ = v_s_1905_;
v_pos_1928_ = v_pos_1906_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1932_; lean_object* v_pos_1933_; 
v___x_1932_ = l_Lean_Parser_whitespace(v_c_1904_, v_s_1905_);
v_pos_1933_ = lean_ctor_get(v___x_1932_, 2);
lean_inc(v_pos_1933_);
v___y_1927_ = v___x_1932_;
v_pos_1928_ = v_pos_1933_;
goto v___jp_1926_;
}
v___jp_1918_:
{
lean_object* v_info_1922_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 3, v_pos_1906_);
lean_ctor_set(v___x_1914_, 2, v___y_1920_);
lean_ctor_set(v___x_1914_, 1, v_startPos_1902_);
lean_ctor_set(v___x_1914_, 0, v_leading_1916_);
v_info_1922_ = v___x_1914_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_leading_1916_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_startPos_1902_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v___y_1920_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_pos_1906_);
v_info_1922_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = l_Lean_Syntax_mkLit(v_n_1901_, v_val_1917_, v_info_1922_);
v___x_1924_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1919_, v___x_1923_);
return v___x_1924_;
}
}
v___jp_1926_:
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_nat_dec_le(v_pos_1928_, v_endPos_1912_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec(v_pos_1928_);
lean_inc(v_pos_1906_);
v___x_1930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1930_, 0, v_inputString_1911_);
lean_ctor_set(v___x_1930_, 1, v_pos_1906_);
lean_ctor_set(v___x_1930_, 2, v_endPos_1912_);
v___y_1919_ = v___y_1927_;
v___y_1920_ = v___x_1930_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1931_; 
lean_dec(v_endPos_1912_);
lean_inc(v_pos_1906_);
v___x_1931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1931_, 0, v_inputString_1911_);
lean_ctor_set(v___x_1931_, 1, v_pos_1906_);
lean_ctor_set(v___x_1931_, 2, v_pos_1928_);
v___y_1919_ = v___y_1927_;
v___y_1920_ = v___x_1931_;
goto v___jp_1918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1937_, lean_object* v_startPos_1938_, lean_object* v_includeWhitespace_1939_, lean_object* v_c_1940_, lean_object* v_s_1941_){
_start:
{
uint8_t v_includeWhitespace_boxed_1942_; lean_object* v_res_1943_; 
v_includeWhitespace_boxed_1942_ = lean_unbox(v_includeWhitespace_1939_);
v_res_1943_ = l_Lean_Parser_mkNodeToken(v_n_1937_, v_startPos_1938_, v_includeWhitespace_boxed_1942_, v_c_1940_, v_s_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1948_, lean_object* v_c_1949_, lean_object* v_s_1950_){
_start:
{
lean_object* v_pos_1951_; lean_object* v_toInputContext_1952_; uint8_t v___x_1953_; 
v_pos_1951_ = lean_ctor_get(v_s_1950_, 2);
v_toInputContext_1952_ = lean_ctor_get(v_c_1949_, 0);
v___x_1953_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1952_, v_pos_1951_);
if (v___x_1953_ == 0)
{
lean_object* v_inputString_1954_; uint8_t v___x_1955_; lean_object* v___y_1957_; uint32_t v_curr_1972_; lean_object* v___x_1973_; lean_object* v_s_1974_; uint32_t v___x_1975_; uint8_t v___x_1976_; 
v_inputString_1954_ = lean_ctor_get(v_toInputContext_1952_, 0);
v___x_1955_ = 1;
v_curr_1972_ = lean_string_utf8_get_fast(v_inputString_1954_, v_pos_1951_);
v___x_1973_ = lean_string_utf8_next_fast(v_inputString_1954_, v_pos_1951_);
v_s_1974_ = l_Lean_Parser_ParserState_setPos(v_s_1950_, v___x_1973_);
v___x_1975_ = 92;
v___x_1976_ = lean_uint32_dec_eq(v_curr_1972_, v___x_1975_);
if (v___x_1976_ == 0)
{
v___y_1957_ = v_s_1974_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1977_; 
lean_inc_ref(v_c_1949_);
v___x_1977_ = l_Lean_Parser_quotedCharFn(v_c_1949_, v_s_1974_);
v___y_1957_ = v___x_1977_;
goto v___jp_1956_;
}
v___jp_1956_:
{
lean_object* v_pos_1958_; lean_object* v_errorMsg_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v_pos_1958_ = lean_ctor_get(v___y_1957_, 2);
v_errorMsg_1959_ = lean_ctor_get(v___y_1957_, 4);
v___x_1960_ = lean_box(0);
lean_inc(v_errorMsg_1959_);
v___x_1961_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_dec_ref(v_c_1949_);
lean_dec(v_startPos_1948_);
return v___y_1957_;
}
else
{
if (v___x_1953_ == 0)
{
uint32_t v_curr_1962_; lean_object* v___x_1963_; lean_object* v_s_1964_; uint32_t v___x_1965_; uint8_t v___x_1966_; 
v_curr_1962_ = lean_string_utf8_get(v_inputString_1954_, v_pos_1958_);
v___x_1963_ = lean_string_utf8_next(v_inputString_1954_, v_pos_1958_);
v_s_1964_ = l_Lean_Parser_ParserState_setPos(v___y_1957_, v___x_1963_);
v___x_1965_ = 39;
v___x_1966_ = lean_uint32_dec_eq(v_curr_1962_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v_c_1949_);
lean_dec(v_startPos_1948_);
v___x_1967_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1968_ = lean_box(0);
v___x_1969_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1964_, v___x_1967_, v___x_1968_, v___x_1955_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1971_ = l_Lean_Parser_mkNodeToken(v___x_1970_, v_startPos_1948_, v___x_1955_, v_c_1949_, v_s_1964_);
return v___x_1971_;
}
}
else
{
lean_dec_ref(v_c_1949_);
lean_dec(v_startPos_1948_);
return v___y_1957_;
}
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_c_1949_);
lean_dec(v_startPos_1948_);
v___x_1978_ = lean_box(0);
v___x_1979_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1950_, v___x_1978_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_1984_, lean_object* v_includeWhitespace_1985_, lean_object* v_c_1986_, lean_object* v_s_1987_){
_start:
{
uint8_t v_includeWhitespace_boxed_1988_; lean_object* v_res_1989_; 
v_includeWhitespace_boxed_1988_ = lean_unbox(v_includeWhitespace_1985_);
v_res_1989_ = l_Lean_Parser_strLitFnAux(v_startPos_1984_, v_includeWhitespace_boxed_1988_, v_c_1986_, v_s_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_1990_, uint8_t v_includeWhitespace_1991_, lean_object* v_c_1992_, lean_object* v_s_1993_){
_start:
{
lean_object* v_pos_1994_; lean_object* v_toInputContext_1995_; uint8_t v___x_1996_; 
v_pos_1994_ = lean_ctor_get(v_s_1993_, 2);
v_toInputContext_1995_ = lean_ctor_get(v_c_1992_, 0);
v___x_1996_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1995_, v_pos_1994_);
if (v___x_1996_ == 0)
{
lean_object* v_inputString_1997_; uint32_t v_curr_1998_; lean_object* v___x_1999_; lean_object* v_s_2000_; uint32_t v___x_2001_; uint8_t v___x_2002_; 
v_inputString_1997_ = lean_ctor_get(v_toInputContext_1995_, 0);
v_curr_1998_ = lean_string_utf8_get_fast(v_inputString_1997_, v_pos_1994_);
v___x_1999_ = lean_string_utf8_next_fast(v_inputString_1997_, v_pos_1994_);
v_s_2000_ = l_Lean_Parser_ParserState_setPos(v_s_1993_, v___x_1999_);
v___x_2001_ = 34;
v___x_2002_ = lean_uint32_dec_eq(v_curr_1998_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint32_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = 92;
v___x_2004_ = lean_uint32_dec_eq(v_curr_1998_, v___x_2003_);
if (v___x_2004_ == 0)
{
v_s_1993_ = v_s_2000_;
goto _start;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2007_ = lean_box(v___x_2004_);
v___x_2008_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2008_, 0, v_startPos_1990_);
lean_closure_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Lean_Parser_andthenFn(v___x_2006_, v___x_2008_, v_c_1992_, v_s_2000_);
return v___x_2009_;
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2011_ = l_Lean_Parser_mkNodeToken(v___x_2010_, v_startPos_1990_, v_includeWhitespace_1991_, v_c_1992_, v_s_2000_);
return v___x_2011_;
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v_c_1992_);
v___x_2012_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2013_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_1993_, v___x_2012_, v_startPos_1990_);
return v___x_2013_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2014_, lean_object* v_i_2015_){
_start:
{
lean_object* v_toInputContext_2016_; uint8_t v___x_2017_; 
v_toInputContext_2016_ = lean_ctor_get(v_c_2014_, 0);
v___x_2017_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2016_, v_i_2015_);
if (v___x_2017_ == 0)
{
lean_object* v_inputString_2018_; uint32_t v_curr_2019_; uint32_t v___x_2020_; uint8_t v___x_2021_; 
v_inputString_2018_ = lean_ctor_get(v_toInputContext_2016_, 0);
v_curr_2019_ = lean_string_utf8_get_fast(v_inputString_2018_, v_i_2015_);
v___x_2020_ = 35;
v___x_2021_ = lean_uint32_dec_eq(v_curr_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
uint32_t v___x_2022_; uint8_t v___x_2023_; 
lean_dec(v_i_2015_);
v___x_2022_ = 34;
v___x_2023_ = lean_uint32_dec_eq(v_curr_2019_, v___x_2022_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_string_utf8_next_fast(v_inputString_2018_, v_i_2015_);
lean_dec(v_i_2015_);
v_i_2015_ = v___x_2024_;
goto _start;
}
}
else
{
uint8_t v___x_2026_; 
lean_dec(v_i_2015_);
v___x_2026_ = 0;
return v___x_2026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2027_, lean_object* v_i_2028_){
_start:
{
uint8_t v_res_2029_; lean_object* v_r_2030_; 
v_res_2029_ = l_Lean_Parser_isRawStrLitStart(v_c_2027_, v_i_2028_);
lean_dec_ref(v_c_2027_);
v_r_2030_ = lean_box(v_res_2029_);
return v_r_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2032_, lean_object* v_s_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2035_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2033_, v___x_2034_, v_startPos_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2036_, lean_object* v_num_2037_, lean_object* v_closingNum_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_pos_2041_; lean_object* v_toInputContext_2042_; uint8_t v___x_2043_; 
v_pos_2041_ = lean_ctor_get(v_a_2040_, 2);
v_toInputContext_2042_ = lean_ctor_get(v_a_2039_, 0);
v___x_2043_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2042_, v_pos_2041_);
if (v___x_2043_ == 0)
{
lean_object* v_inputString_2044_; uint32_t v_curr_2045_; lean_object* v___x_2046_; lean_object* v_s_2047_; uint32_t v___x_2048_; uint8_t v___x_2049_; 
v_inputString_2044_ = lean_ctor_get(v_toInputContext_2042_, 0);
v_curr_2045_ = lean_string_utf8_get_fast(v_inputString_2044_, v_pos_2041_);
v___x_2046_ = lean_string_utf8_next_fast(v_inputString_2044_, v_pos_2041_);
v_s_2047_ = l_Lean_Parser_ParserState_setPos(v_a_2040_, v___x_2046_);
v___x_2048_ = 35;
v___x_2049_ = lean_uint32_dec_eq(v_curr_2045_, v___x_2048_);
if (v___x_2049_ == 0)
{
uint32_t v___x_2050_; uint8_t v___x_2051_; 
lean_dec(v_closingNum_2038_);
v___x_2050_ = 34;
v___x_2051_ = lean_uint32_dec_eq(v_curr_2045_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2036_, v_num_2037_, v_a_2039_, v_s_2047_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v_closingNum_2038_ = v___x_2053_;
v_a_2040_ = v_s_2047_;
goto _start;
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_add(v_closingNum_2038_, v___x_2055_);
lean_dec(v_closingNum_2038_);
v___x_2057_ = lean_nat_dec_eq(v___x_2056_, v_num_2037_);
if (v___x_2057_ == 0)
{
v_closingNum_2038_ = v___x_2056_;
v_a_2040_ = v_s_2047_;
goto _start;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec(v___x_2056_);
v___x_2059_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2060_ = l_Lean_Parser_mkNodeToken(v___x_2059_, v_startPos_2036_, v___x_2057_, v_a_2039_, v_s_2047_);
return v___x_2060_;
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec_ref(v_a_2039_);
lean_dec(v_closingNum_2038_);
v___x_2061_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2036_, v_a_2040_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2062_, lean_object* v_num_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_pos_2066_; lean_object* v_toInputContext_2067_; uint8_t v___x_2068_; 
v_pos_2066_ = lean_ctor_get(v_a_2065_, 2);
v_toInputContext_2067_ = lean_ctor_get(v_a_2064_, 0);
v___x_2068_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2067_, v_pos_2066_);
if (v___x_2068_ == 0)
{
lean_object* v_inputString_2069_; uint32_t v_curr_2070_; lean_object* v___x_2071_; lean_object* v_s_2072_; uint32_t v___x_2073_; uint8_t v___x_2074_; 
v_inputString_2069_ = lean_ctor_get(v_toInputContext_2067_, 0);
v_curr_2070_ = lean_string_utf8_get_fast(v_inputString_2069_, v_pos_2066_);
v___x_2071_ = lean_string_utf8_next_fast(v_inputString_2069_, v_pos_2066_);
v_s_2072_ = l_Lean_Parser_ParserState_setPos(v_a_2065_, v___x_2071_);
v___x_2073_ = 34;
v___x_2074_ = lean_uint32_dec_eq(v_curr_2070_, v___x_2073_);
if (v___x_2074_ == 0)
{
v_a_2065_ = v_s_2072_;
goto _start;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_nat_dec_eq(v_num_2063_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2062_, v_num_2063_, v___x_2076_, v_a_2064_, v_s_2072_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2080_ = l_Lean_Parser_mkNodeToken(v___x_2079_, v_startPos_2062_, v___x_2077_, v_a_2064_, v_s_2072_);
return v___x_2080_;
}
}
}
else
{
lean_object* v___x_2081_; 
lean_dec_ref(v_a_2064_);
v___x_2081_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2062_, v_a_2065_);
return v___x_2081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2082_, lean_object* v_num_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2082_, v_num_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_num_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2087_, lean_object* v_num_2088_, lean_object* v_closingNum_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2087_, v_num_2088_, v_closingNum_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_num_2088_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2093_, lean_object* v_num_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_pos_2097_; lean_object* v_toInputContext_2098_; uint8_t v___x_2099_; 
v_pos_2097_ = lean_ctor_get(v_a_2096_, 2);
v_toInputContext_2098_ = lean_ctor_get(v_a_2095_, 0);
v___x_2099_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2098_, v_pos_2097_);
if (v___x_2099_ == 0)
{
lean_object* v_inputString_2100_; uint32_t v_curr_2101_; lean_object* v___x_2102_; lean_object* v_s_2103_; uint32_t v___x_2104_; uint8_t v___x_2105_; 
v_inputString_2100_ = lean_ctor_get(v_toInputContext_2098_, 0);
v_curr_2101_ = lean_string_utf8_get_fast(v_inputString_2100_, v_pos_2097_);
v___x_2102_ = lean_string_utf8_next_fast(v_inputString_2100_, v_pos_2097_);
v_s_2103_ = l_Lean_Parser_ParserState_setPos(v_a_2096_, v___x_2102_);
v___x_2104_ = 35;
v___x_2105_ = lean_uint32_dec_eq(v_curr_2101_, v___x_2104_);
if (v___x_2105_ == 0)
{
uint32_t v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = 34;
v___x_2107_ = lean_uint32_dec_eq(v_curr_2101_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec_ref(v_a_2095_);
lean_dec(v_num_2094_);
v___x_2108_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2093_, v_s_2103_);
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2093_, v_num_2094_, v_a_2095_, v_s_2103_);
lean_dec(v_num_2094_);
return v___x_2109_;
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = lean_nat_add(v_num_2094_, v___x_2110_);
lean_dec(v_num_2094_);
v_num_2094_ = v___x_2111_;
v_a_2096_ = v_s_2103_;
goto _start;
}
}
else
{
lean_object* v___x_2113_; 
lean_dec_ref(v_a_2095_);
lean_dec(v_num_2094_);
v___x_2113_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2093_, v_a_2096_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2114_, v___x_2117_, v_a_2115_, v_a_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2120_, lean_object* v_expecting_2121_, uint8_t v_needDigit_2122_, lean_object* v_c_2123_, lean_object* v_s_2124_){
_start:
{
lean_object* v_pos_2125_; lean_object* v_toInputContext_2126_; uint8_t v___x_2127_; 
v_pos_2125_ = lean_ctor_get(v_s_2124_, 2);
v_toInputContext_2126_ = lean_ctor_get(v_c_2123_, 0);
v___x_2127_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2126_, v_pos_2125_);
if (v___x_2127_ == 0)
{
lean_object* v_inputString_2128_; uint8_t v___x_2129_; uint32_t v_curr_2130_; uint32_t v___x_2131_; uint8_t v___x_2132_; 
v_inputString_2128_ = lean_ctor_get(v_toInputContext_2126_, 0);
v___x_2129_ = 1;
v_curr_2130_ = lean_string_utf8_get_fast(v_inputString_2128_, v_pos_2125_);
v___x_2131_ = 95;
v___x_2132_ = lean_uint32_dec_eq(v_curr_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2133_ = lean_box_uint32(v_curr_2130_);
lean_inc_ref(v_isDigit_2120_);
v___x_2134_ = lean_apply_1(v_isDigit_2120_, v___x_2133_);
v___x_2135_ = lean_unbox(v___x_2134_);
if (v___x_2135_ == 0)
{
lean_dec_ref(v_isDigit_2120_);
if (v_needDigit_2122_ == 0)
{
lean_dec_ref(v_expecting_2121_);
return v_s_2124_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2136_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2137_ = lean_box(0);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_expecting_2121_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2124_, v___x_2136_, v___x_2138_, v___x_2129_);
return v___x_2139_;
}
}
else
{
lean_object* v___x_2140_; 
lean_inc(v_pos_2125_);
v___x_2140_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2124_, v_c_2123_, v_pos_2125_);
lean_dec(v_pos_2125_);
v_needDigit_2122_ = v___x_2132_;
v_s_2124_ = v___x_2140_;
goto _start;
}
}
else
{
lean_object* v___x_2142_; 
lean_inc(v_pos_2125_);
v___x_2142_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2124_, v_c_2123_, v_pos_2125_);
lean_dec(v_pos_2125_);
v_needDigit_2122_ = v___x_2129_;
v_s_2124_ = v___x_2142_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2120_);
if (v_needDigit_2122_ == 0)
{
lean_dec_ref(v_expecting_2121_);
return v_s_2124_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_expecting_2121_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2124_, v___x_2145_);
return v___x_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2147_, lean_object* v_expecting_2148_, lean_object* v_needDigit_2149_, lean_object* v_c_2150_, lean_object* v_s_2151_){
_start:
{
uint8_t v_needDigit_boxed_2152_; lean_object* v_res_2153_; 
v_needDigit_boxed_2152_ = lean_unbox(v_needDigit_2149_);
v_res_2153_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2147_, v_expecting_2148_, v_needDigit_boxed_2152_, v_c_2150_, v_s_2151_);
lean_dec_ref(v_c_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2154_){
_start:
{
uint32_t v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = 48;
v___x_2156_ = lean_uint32_dec_le(v___x_2155_, v_c_2154_);
if (v___x_2156_ == 0)
{
return v___x_2156_;
}
else
{
uint32_t v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = 57;
v___x_2158_ = lean_uint32_dec_le(v_c_2154_, v___x_2157_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2159_){
_start:
{
uint32_t v_c_boxed_2160_; uint8_t v_res_2161_; lean_object* v_r_2162_; 
v_c_boxed_2160_ = lean_unbox_uint32(v_c_2159_);
lean_dec(v_c_2159_);
v_res_2161_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2160_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2167_, lean_object* v_c_2168_, lean_object* v_s_2169_, uint8_t v_hasBareDot_2170_){
_start:
{
lean_object* v_toInputContext_2171_; lean_object* v_pos_2172_; uint8_t v___x_2173_; 
v_toInputContext_2171_ = lean_ctor_get(v_c_2168_, 0);
v_pos_2172_ = lean_ctor_get(v_s_2169_, 2);
v___x_2173_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2171_, v_pos_2172_);
if (v___x_2173_ == 0)
{
lean_object* v_inputString_2174_; lean_object* v___f_2175_; uint8_t v___x_2176_; lean_object* v___y_2178_; uint8_t v___y_2179_; lean_object* v___y_2187_; lean_object* v___y_2194_; lean_object* v___y_2195_; uint8_t v___y_2210_; uint32_t v_curr_2211_; uint8_t v___y_2213_; uint32_t v___x_2222_; uint8_t v___x_2223_; 
v_inputString_2174_ = lean_ctor_get(v_toInputContext_2171_, 0);
v___f_2175_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2176_ = 1;
v_curr_2211_ = lean_string_utf8_get_fast(v_inputString_2174_, v_pos_2172_);
v___x_2222_ = 101;
v___x_2223_ = lean_uint32_dec_eq(v_curr_2211_, v___x_2222_);
if (v___x_2223_ == 0)
{
uint32_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = 69;
v___x_2225_ = lean_uint32_dec_eq(v_curr_2211_, v___x_2224_);
if (v___x_2225_ == 0)
{
if (v_hasBareDot_2170_ == 0)
{
lean_dec(v_startPos_2167_);
return v_s_2169_;
}
else
{
uint32_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = 65;
v___x_2227_ = lean_uint32_dec_le(v___x_2226_, v_curr_2211_);
if (v___x_2227_ == 0)
{
goto v___jp_2217_;
}
else
{
uint32_t v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = 90;
v___x_2229_ = lean_uint32_dec_le(v_curr_2211_, v___x_2228_);
if (v___x_2229_ == 0)
{
goto v___jp_2217_;
}
else
{
goto v___jp_2204_;
}
}
}
}
else
{
lean_dec(v_startPos_2167_);
goto v___jp_2197_;
}
}
else
{
lean_dec(v_startPos_2167_);
goto v___jp_2197_;
}
v___jp_2177_:
{
if (v___y_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v___y_2178_);
v___x_2180_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2169_, v___x_2180_, v___x_2181_, v___x_2176_);
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2184_ = l_Lean_Parser_ParserState_setPos(v_s_2169_, v___y_2178_);
v___x_2185_ = l_Lean_Parser_takeDigitsFn(v___f_2175_, v___x_2183_, v___x_2173_, v_c_2168_, v___x_2184_);
return v___x_2185_;
}
}
v___jp_2186_:
{
uint32_t v_curr_2188_; uint32_t v___x_2189_; uint8_t v___x_2190_; 
v_curr_2188_ = lean_string_utf8_get(v_inputString_2174_, v___y_2187_);
v___x_2189_ = 48;
v___x_2190_ = lean_uint32_dec_le(v___x_2189_, v_curr_2188_);
if (v___x_2190_ == 0)
{
v___y_2178_ = v___y_2187_;
v___y_2179_ = v___x_2190_;
goto v___jp_2177_;
}
else
{
uint32_t v___x_2191_; uint8_t v___x_2192_; 
v___x_2191_ = 57;
v___x_2192_ = lean_uint32_dec_le(v_curr_2188_, v___x_2191_);
v___y_2178_ = v___y_2187_;
v___y_2179_ = v___x_2192_;
goto v___jp_2177_;
}
}
v___jp_2193_:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_string_utf8_next(v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
v___y_2187_ = v___x_2196_;
goto v___jp_2186_;
}
v___jp_2197_:
{
lean_object* v_i_2198_; uint32_t v___x_2199_; uint32_t v___x_2200_; uint8_t v___x_2201_; 
v_i_2198_ = lean_string_utf8_next(v_inputString_2174_, v_pos_2172_);
v___x_2199_ = lean_string_utf8_get(v_inputString_2174_, v_i_2198_);
v___x_2200_ = 45;
v___x_2201_ = lean_uint32_dec_eq(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
uint32_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = 43;
v___x_2203_ = lean_uint32_dec_eq(v___x_2199_, v___x_2202_);
if (v___x_2203_ == 0)
{
v___y_2187_ = v_i_2198_;
goto v___jp_2186_;
}
else
{
v___y_2194_ = v_inputString_2174_;
v___y_2195_ = v_i_2198_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v_inputString_2174_;
v___y_2195_ = v_i_2198_;
goto v___jp_2193_;
}
}
v___jp_2204_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lean_Parser_ParserState_setPos(v_s_2169_, v_startPos_2167_);
v___x_2206_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2207_ = lean_box(0);
v___x_2208_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2205_, v___x_2206_, v___x_2207_, v___x_2176_);
return v___x_2208_;
}
v___jp_2209_:
{
if (v___y_2210_ == 0)
{
lean_dec(v_startPos_2167_);
return v_s_2169_;
}
else
{
goto v___jp_2204_;
}
}
v___jp_2212_:
{
if (v___y_2213_ == 0)
{
uint32_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = 95;
v___x_2215_ = lean_uint32_dec_eq(v_curr_2211_, v___x_2214_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
v___x_2216_ = l_Lean_isLetterLike(v_curr_2211_);
v___y_2210_ = v___x_2216_;
goto v___jp_2209_;
}
else
{
v___y_2210_ = v___x_2215_;
goto v___jp_2209_;
}
}
else
{
goto v___jp_2204_;
}
}
v___jp_2217_:
{
uint32_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = 97;
v___x_2219_ = lean_uint32_dec_le(v___x_2218_, v_curr_2211_);
if (v___x_2219_ == 0)
{
v___y_2213_ = v___x_2219_;
goto v___jp_2212_;
}
else
{
uint32_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = 122;
v___x_2221_ = lean_uint32_dec_le(v_curr_2211_, v___x_2220_);
v___y_2213_ = v___x_2221_;
goto v___jp_2212_;
}
}
}
else
{
lean_dec(v_startPos_2167_);
return v_s_2169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2230_, lean_object* v_c_2231_, lean_object* v_s_2232_, lean_object* v_hasBareDot_2233_){
_start:
{
uint8_t v_hasBareDot_boxed_2234_; lean_object* v_res_2235_; 
v_hasBareDot_boxed_2234_ = lean_unbox(v_hasBareDot_2233_);
v_res_2235_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2230_, v_c_2231_, v_s_2232_, v_hasBareDot_boxed_2234_);
lean_dec_ref(v_c_2231_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2236_, lean_object* v_s_2237_){
_start:
{
lean_object* v_toInputContext_2238_; lean_object* v_pos_2239_; lean_object* v_inputString_2240_; uint32_t v_curr_2241_; uint32_t v___x_2242_; uint8_t v___x_2243_; 
v_toInputContext_2238_ = lean_ctor_get(v_c_2236_, 0);
v_pos_2239_ = lean_ctor_get(v_s_2237_, 2);
v_inputString_2240_ = lean_ctor_get(v_toInputContext_2238_, 0);
v_curr_2241_ = lean_string_utf8_get(v_inputString_2240_, v_pos_2239_);
v___x_2242_ = 46;
v___x_2243_ = lean_uint32_dec_eq(v_curr_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_box(v___x_2243_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v_s_2237_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
return v___x_2245_;
}
else
{
lean_object* v___f_2246_; lean_object* v_i_2247_; uint8_t v___y_2249_; uint32_t v_curr_2259_; uint32_t v___x_2260_; uint8_t v___x_2261_; 
v___f_2246_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_i_2247_ = lean_string_utf8_next(v_inputString_2240_, v_pos_2239_);
v_curr_2259_ = lean_string_utf8_get(v_inputString_2240_, v_i_2247_);
v___x_2260_ = 48;
v___x_2261_ = lean_uint32_dec_le(v___x_2260_, v_curr_2259_);
if (v___x_2261_ == 0)
{
v___y_2249_ = v___x_2261_;
goto v___jp_2248_;
}
else
{
uint32_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = 57;
v___x_2263_ = lean_uint32_dec_le(v_curr_2259_, v___x_2262_);
v___y_2249_ = v___x_2263_;
goto v___jp_2248_;
}
v___jp_2248_:
{
if (v___y_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = l_Lean_Parser_ParserState_setPos(v_s_2237_, v_i_2247_);
v___x_2251_ = lean_box(v___x_2243_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2254_ = 0;
v___x_2255_ = l_Lean_Parser_ParserState_setPos(v_s_2237_, v_i_2247_);
v___x_2256_ = l_Lean_Parser_takeDigitsFn(v___f_2246_, v___x_2253_, v___x_2254_, v_c_2236_, v___x_2255_);
v___x_2257_ = lean_box(v___x_2254_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
return v___x_2258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2264_, lean_object* v_s_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2264_, v_s_2265_);
lean_dec_ref(v_c_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2270_, uint8_t v_includeWhitespace_2271_, lean_object* v_c_2272_, lean_object* v_s_2273_){
_start:
{
lean_object* v___x_2274_; lean_object* v_fst_2275_; lean_object* v_snd_2276_; uint8_t v___x_2277_; lean_object* v_s_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2274_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2272_, v_s_2273_);
v_fst_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_fst_2275_);
v_snd_2276_ = lean_ctor_get(v___x_2274_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v___x_2274_);
v___x_2277_ = lean_unbox(v_snd_2276_);
lean_dec(v_snd_2276_);
lean_inc(v_startPos_2270_);
v_s_2278_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2270_, v_c_2272_, v_fst_2275_, v___x_2277_);
v___x_2279_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2280_ = l_Lean_Parser_mkNodeToken(v___x_2279_, v_startPos_2270_, v_includeWhitespace_2271_, v_c_2272_, v_s_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2281_, lean_object* v_includeWhitespace_2282_, lean_object* v_c_2283_, lean_object* v_s_2284_){
_start:
{
uint8_t v_includeWhitespace_boxed_2285_; lean_object* v_res_2286_; 
v_includeWhitespace_boxed_2285_ = lean_unbox(v_includeWhitespace_2282_);
v_res_2286_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2281_, v_includeWhitespace_boxed_2285_, v_c_2283_, v_s_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2290_, uint8_t v_includeWhitespace_2291_, lean_object* v_c_2292_, lean_object* v_s_2293_){
_start:
{
lean_object* v___f_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; lean_object* v_s_2297_; lean_object* v_pos_2298_; lean_object* v_toInputContext_2299_; uint8_t v___x_2300_; 
v___f_2294_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2295_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2296_ = 0;
v_s_2297_ = l_Lean_Parser_takeDigitsFn(v___f_2294_, v___x_2295_, v___x_2296_, v_c_2292_, v_s_2293_);
v_pos_2298_ = lean_ctor_get(v_s_2297_, 2);
lean_inc(v_pos_2298_);
v_toInputContext_2299_ = lean_ctor_get(v_c_2292_, 0);
v___x_2300_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2299_, v_pos_2298_);
if (v___x_2300_ == 0)
{
lean_object* v_inputString_2301_; uint32_t v_curr_2302_; uint8_t v___y_2316_; lean_object* v_j_2319_; uint8_t v___x_2325_; 
v_inputString_2301_ = lean_ctor_get(v_toInputContext_2299_, 0);
v_curr_2302_ = lean_string_utf8_get_fast(v_inputString_2301_, v_pos_2298_);
v_j_2319_ = lean_string_utf8_next(v_inputString_2301_, v_pos_2298_);
lean_dec(v_pos_2298_);
v___x_2325_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2299_, v_j_2319_);
if (v___x_2325_ == 0)
{
goto v___jp_2320_;
}
else
{
if (v___x_2300_ == 0)
{
lean_dec(v_j_2319_);
goto v___jp_2303_;
}
else
{
goto v___jp_2320_;
}
}
v___jp_2303_:
{
uint32_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = 46;
v___x_2305_ = lean_uint32_dec_eq(v_curr_2302_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint32_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = 101;
v___x_2307_ = lean_uint32_dec_eq(v_curr_2302_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint32_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = 69;
v___x_2309_ = lean_uint32_dec_eq(v_curr_2302_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2311_ = l_Lean_Parser_mkNodeToken(v___x_2310_, v_startPos_2290_, v_includeWhitespace_2291_, v_c_2292_, v_s_2297_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2290_, v_includeWhitespace_2291_, v_c_2292_, v_s_2297_);
return v___x_2312_;
}
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2290_, v_includeWhitespace_2291_, v_c_2292_, v_s_2297_);
return v___x_2313_;
}
}
else
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2290_, v_includeWhitespace_2291_, v_c_2292_, v_s_2297_);
return v___x_2314_;
}
}
v___jp_2315_:
{
if (v___y_2316_ == 0)
{
goto v___jp_2303_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2318_ = l_Lean_Parser_mkNodeToken(v___x_2317_, v_startPos_2290_, v_includeWhitespace_2291_, v_c_2292_, v_s_2297_);
return v___x_2318_;
}
}
v___jp_2320_:
{
uint32_t v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = 46;
v___x_2322_ = lean_uint32_dec_eq(v_curr_2302_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_dec(v_j_2319_);
v___y_2316_ = v___x_2322_;
goto v___jp_2315_;
}
else
{
uint32_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = lean_string_utf8_get_fast(v_inputString_2301_, v_j_2319_);
lean_dec(v_j_2319_);
v___x_2324_ = lean_uint32_dec_eq(v___x_2323_, v___x_2321_);
v___y_2316_ = v___x_2324_;
goto v___jp_2315_;
}
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v_pos_2298_);
v___x_2326_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2327_ = l_Lean_Parser_mkNodeToken(v___x_2326_, v_startPos_2290_, v___x_2300_, v_c_2292_, v_s_2297_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2328_, lean_object* v_includeWhitespace_2329_, lean_object* v_c_2330_, lean_object* v_s_2331_){
_start:
{
uint8_t v_includeWhitespace_boxed_2332_; lean_object* v_res_2333_; 
v_includeWhitespace_boxed_2332_ = lean_unbox(v_includeWhitespace_2329_);
v_res_2333_ = l_Lean_Parser_decimalNumberFn(v_startPos_2328_, v_includeWhitespace_boxed_2332_, v_c_2330_, v_s_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2334_){
_start:
{
uint32_t v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = 48;
v___x_2336_ = lean_uint32_dec_eq(v_c_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
uint32_t v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = 49;
v___x_2338_ = lean_uint32_dec_eq(v_c_2334_, v___x_2337_);
return v___x_2338_;
}
else
{
return v___x_2336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2339_){
_start:
{
uint32_t v_c_boxed_2340_; uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_c_boxed_2340_ = lean_unbox_uint32(v_c_2339_);
lean_dec(v_c_2339_);
v_res_2341_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2340_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2345_, uint8_t v_includeWhitespace_2346_, lean_object* v_c_2347_, lean_object* v_s_2348_){
_start:
{
lean_object* v___f_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; lean_object* v_s_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___f_2349_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2350_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2351_ = 1;
v_s_2352_ = l_Lean_Parser_takeDigitsFn(v___f_2349_, v___x_2350_, v___x_2351_, v_c_2347_, v_s_2348_);
v___x_2353_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2354_ = l_Lean_Parser_mkNodeToken(v___x_2353_, v_startPos_2345_, v_includeWhitespace_2346_, v_c_2347_, v_s_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2355_, lean_object* v_includeWhitespace_2356_, lean_object* v_c_2357_, lean_object* v_s_2358_){
_start:
{
uint8_t v_includeWhitespace_boxed_2359_; lean_object* v_res_2360_; 
v_includeWhitespace_boxed_2359_ = lean_unbox(v_includeWhitespace_2356_);
v_res_2360_ = l_Lean_Parser_binNumberFn(v_startPos_2355_, v_includeWhitespace_boxed_2359_, v_c_2357_, v_s_2358_);
return v_res_2360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2361_){
_start:
{
uint32_t v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = 48;
v___x_2363_ = lean_uint32_dec_le(v___x_2362_, v_c_2361_);
if (v___x_2363_ == 0)
{
return v___x_2363_;
}
else
{
uint32_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = 55;
v___x_2365_ = lean_uint32_dec_le(v_c_2361_, v___x_2364_);
return v___x_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2366_){
_start:
{
uint32_t v_c_boxed_2367_; uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_c_boxed_2367_ = lean_unbox_uint32(v_c_2366_);
lean_dec(v_c_2366_);
v_res_2368_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2367_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2372_, uint8_t v_includeWhitespace_2373_, lean_object* v_c_2374_, lean_object* v_s_2375_){
_start:
{
lean_object* v___f_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; lean_object* v_s_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___f_2376_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2377_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2378_ = 1;
v_s_2379_ = l_Lean_Parser_takeDigitsFn(v___f_2376_, v___x_2377_, v___x_2378_, v_c_2374_, v_s_2375_);
v___x_2380_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2381_ = l_Lean_Parser_mkNodeToken(v___x_2380_, v_startPos_2372_, v_includeWhitespace_2373_, v_c_2374_, v_s_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2382_, lean_object* v_includeWhitespace_2383_, lean_object* v_c_2384_, lean_object* v_s_2385_){
_start:
{
uint8_t v_includeWhitespace_boxed_2386_; lean_object* v_res_2387_; 
v_includeWhitespace_boxed_2386_ = lean_unbox(v_includeWhitespace_2383_);
v_res_2387_ = l_Lean_Parser_octalNumberFn(v_startPos_2382_, v_includeWhitespace_boxed_2386_, v_c_2384_, v_s_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2388_){
_start:
{
uint8_t v___y_2390_; uint8_t v___y_2396_; uint32_t v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = 48;
v___x_2402_ = lean_uint32_dec_le(v___x_2401_, v_c_2388_);
if (v___x_2402_ == 0)
{
v___y_2396_ = v___x_2402_;
goto v___jp_2395_;
}
else
{
uint32_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = 57;
v___x_2404_ = lean_uint32_dec_le(v_c_2388_, v___x_2403_);
v___y_2396_ = v___x_2404_;
goto v___jp_2395_;
}
v___jp_2389_:
{
if (v___y_2390_ == 0)
{
uint32_t v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = 65;
v___x_2392_ = lean_uint32_dec_le(v___x_2391_, v_c_2388_);
if (v___x_2392_ == 0)
{
return v___x_2392_;
}
else
{
uint32_t v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = 70;
v___x_2394_ = lean_uint32_dec_le(v_c_2388_, v___x_2393_);
return v___x_2394_;
}
}
else
{
return v___y_2390_;
}
}
v___jp_2395_:
{
if (v___y_2396_ == 0)
{
uint32_t v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = 97;
v___x_2398_ = lean_uint32_dec_le(v___x_2397_, v_c_2388_);
if (v___x_2398_ == 0)
{
v___y_2390_ = v___x_2398_;
goto v___jp_2389_;
}
else
{
uint32_t v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = 102;
v___x_2400_ = lean_uint32_dec_le(v_c_2388_, v___x_2399_);
v___y_2390_ = v___x_2400_;
goto v___jp_2389_;
}
}
else
{
return v___y_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2405_){
_start:
{
uint32_t v_c_boxed_2406_; uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_c_boxed_2406_ = lean_unbox_uint32(v_c_2405_);
lean_dec(v_c_2405_);
v_res_2407_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2406_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2409_){
_start:
{
uint8_t v___y_2411_; uint8_t v___y_2417_; uint32_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = 48;
v___x_2423_ = lean_uint32_dec_le(v___x_2422_, v___y_2409_);
if (v___x_2423_ == 0)
{
v___y_2417_ = v___x_2423_;
goto v___jp_2416_;
}
else
{
uint32_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = 57;
v___x_2425_ = lean_uint32_dec_le(v___y_2409_, v___x_2424_);
v___y_2417_ = v___x_2425_;
goto v___jp_2416_;
}
v___jp_2410_:
{
if (v___y_2411_ == 0)
{
uint32_t v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = 65;
v___x_2413_ = lean_uint32_dec_le(v___x_2412_, v___y_2409_);
if (v___x_2413_ == 0)
{
return v___x_2413_;
}
else
{
uint32_t v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = 70;
v___x_2415_ = lean_uint32_dec_le(v___y_2409_, v___x_2414_);
return v___x_2415_;
}
}
else
{
return v___y_2411_;
}
}
v___jp_2416_:
{
if (v___y_2417_ == 0)
{
uint32_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = 97;
v___x_2419_ = lean_uint32_dec_le(v___x_2418_, v___y_2409_);
if (v___x_2419_ == 0)
{
v___y_2411_ = v___x_2419_;
goto v___jp_2410_;
}
else
{
uint32_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = 102;
v___x_2421_ = lean_uint32_dec_le(v___y_2409_, v___x_2420_);
v___y_2411_ = v___x_2421_;
goto v___jp_2410_;
}
}
else
{
return v___y_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2426_){
_start:
{
uint32_t v___y_54__boxed_2427_; uint8_t v_res_2428_; lean_object* v_r_2429_; 
v___y_54__boxed_2427_ = lean_unbox_uint32(v___y_2426_);
lean_dec(v___y_2426_);
v_res_2428_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_54__boxed_2427_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2432_, uint8_t v_includeWhitespace_2433_, lean_object* v_kind_2434_, lean_object* v_c_2435_, lean_object* v_s_2436_){
_start:
{
lean_object* v___f_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v_s_2440_; lean_object* v___x_2441_; 
v___f_2437_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2438_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2439_ = 1;
v_s_2440_ = l_Lean_Parser_takeDigitsFn(v___f_2437_, v___x_2438_, v___x_2439_, v_c_2435_, v_s_2436_);
v___x_2441_ = l_Lean_Parser_mkNodeToken(v_kind_2434_, v_startPos_2432_, v_includeWhitespace_2433_, v_c_2435_, v_s_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2442_, lean_object* v_includeWhitespace_2443_, lean_object* v_kind_2444_, lean_object* v_c_2445_, lean_object* v_s_2446_){
_start:
{
uint8_t v_includeWhitespace_boxed_2447_; lean_object* v_res_2448_; 
v_includeWhitespace_boxed_2447_ = lean_unbox(v_includeWhitespace_2443_);
v_res_2448_ = l_Lean_Parser_hexNumberFn(v_startPos_2442_, v_includeWhitespace_boxed_2447_, v_kind_2444_, v_c_2445_, v_s_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2450_, lean_object* v_c_2451_, lean_object* v_s_2452_){
_start:
{
lean_object* v_pos_2453_; uint8_t v___y_2455_; lean_object* v_toInputContext_2460_; uint8_t v___x_2461_; 
v_pos_2453_ = lean_ctor_get(v_s_2452_, 2);
v_toInputContext_2460_ = lean_ctor_get(v_c_2451_, 0);
v___x_2461_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2460_, v_pos_2453_);
if (v___x_2461_ == 0)
{
lean_object* v_inputString_2462_; uint32_t v_curr_2463_; uint32_t v___x_2464_; uint8_t v___x_2465_; 
v_inputString_2462_ = lean_ctor_get(v_toInputContext_2460_, 0);
v_curr_2463_ = lean_string_utf8_get_fast(v_inputString_2462_, v_pos_2453_);
v___x_2464_ = 48;
v___x_2465_ = lean_uint32_dec_eq(v_curr_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_uint32_dec_le(v___x_2464_, v_curr_2463_);
if (v___x_2466_ == 0)
{
v___y_2455_ = v___x_2466_;
goto v___jp_2454_;
}
else
{
uint32_t v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = 57;
v___x_2468_ = lean_uint32_dec_le(v_curr_2463_, v___x_2467_);
v___y_2455_ = v___x_2468_;
goto v___jp_2454_;
}
}
else
{
lean_object* v_i_2469_; uint32_t v_curr_2480_; uint32_t v___x_2481_; uint8_t v___x_2482_; 
lean_inc(v_pos_2453_);
v_i_2469_ = lean_string_utf8_next_fast(v_inputString_2462_, v_pos_2453_);
v_curr_2480_ = lean_string_utf8_get(v_inputString_2462_, v_i_2469_);
v___x_2481_ = 98;
v___x_2482_ = lean_uint32_dec_eq(v_curr_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
uint32_t v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = 66;
v___x_2484_ = lean_uint32_dec_eq(v_curr_2480_, v___x_2483_);
if (v___x_2484_ == 0)
{
uint32_t v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = 111;
v___x_2486_ = lean_uint32_dec_eq(v_curr_2480_, v___x_2485_);
if (v___x_2486_ == 0)
{
uint32_t v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = 79;
v___x_2488_ = lean_uint32_dec_eq(v_curr_2480_, v___x_2487_);
if (v___x_2488_ == 0)
{
uint32_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = 120;
v___x_2490_ = lean_uint32_dec_eq(v_curr_2480_, v___x_2489_);
if (v___x_2490_ == 0)
{
uint32_t v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = 88;
v___x_2492_ = lean_uint32_dec_eq(v_curr_2480_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = l_Lean_Parser_ParserState_setPos(v_s_2452_, v_i_2469_);
v___x_2494_ = l_Lean_Parser_decimalNumberFn(v_pos_2453_, v_includeWhitespace_2450_, v_c_2451_, v___x_2493_);
return v___x_2494_;
}
else
{
goto v___jp_2470_;
}
}
else
{
goto v___jp_2470_;
}
}
else
{
goto v___jp_2474_;
}
}
else
{
goto v___jp_2474_;
}
}
else
{
goto v___jp_2477_;
}
}
else
{
goto v___jp_2477_;
}
v___jp_2470_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2472_ = l_Lean_Parser_ParserState_next(v_s_2452_, v_c_2451_, v_i_2469_);
v___x_2473_ = l_Lean_Parser_hexNumberFn(v_pos_2453_, v_includeWhitespace_2450_, v___x_2471_, v_c_2451_, v___x_2472_);
return v___x_2473_;
}
v___jp_2474_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = l_Lean_Parser_ParserState_next(v_s_2452_, v_c_2451_, v_i_2469_);
v___x_2476_ = l_Lean_Parser_octalNumberFn(v_pos_2453_, v_includeWhitespace_2450_, v_c_2451_, v___x_2475_);
return v___x_2476_;
}
v___jp_2477_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = l_Lean_Parser_ParserState_next(v_s_2452_, v_c_2451_, v_i_2469_);
v___x_2479_ = l_Lean_Parser_binNumberFn(v_pos_2453_, v_includeWhitespace_2450_, v_c_2451_, v___x_2478_);
return v___x_2479_;
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec_ref(v_c_2451_);
v___x_2495_ = lean_box(0);
v___x_2496_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2452_, v___x_2495_);
return v___x_2496_;
}
v___jp_2454_:
{
if (v___y_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_dec_ref(v_c_2451_);
v___x_2456_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2457_ = l_Lean_Parser_ParserState_mkError(v_s_2452_, v___x_2456_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_inc(v_pos_2453_);
v___x_2458_ = l_Lean_Parser_ParserState_next(v_s_2452_, v_c_2451_, v_pos_2453_);
v___x_2459_ = l_Lean_Parser_decimalNumberFn(v_pos_2453_, v_includeWhitespace_2450_, v_c_2451_, v___x_2458_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2497_, lean_object* v_c_2498_, lean_object* v_s_2499_){
_start:
{
uint8_t v_includeWhitespace_boxed_2500_; lean_object* v_res_2501_; 
v_includeWhitespace_boxed_2500_ = lean_unbox(v_includeWhitespace_2497_);
v_res_2501_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2500_, v_c_2498_, v_s_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2502_, lean_object* v_s_2503_){
_start:
{
lean_object* v_toInputContext_2504_; lean_object* v_pos_2505_; lean_object* v_inputString_2506_; uint32_t v_curr_2507_; uint32_t v___x_2508_; uint8_t v___x_2509_; 
v_toInputContext_2504_ = lean_ctor_get(v_c_2502_, 0);
v_pos_2505_ = lean_ctor_get(v_s_2503_, 2);
v_inputString_2506_ = lean_ctor_get(v_toInputContext_2504_, 0);
v_curr_2507_ = lean_string_utf8_get(v_inputString_2506_, v_pos_2505_);
v___x_2508_ = 46;
v___x_2509_ = lean_uint32_dec_eq(v_curr_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
return v___x_2509_;
}
else
{
lean_object* v_i_2510_; uint8_t v___x_2511_; 
v_i_2510_ = lean_string_utf8_next(v_inputString_2506_, v_pos_2505_);
v___x_2511_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2504_, v_i_2510_);
if (v___x_2511_ == 0)
{
uint32_t v_curr_2512_; uint8_t v___y_2514_; uint8_t v___y_2518_; uint32_t v___x_2527_; uint8_t v___x_2528_; 
v_curr_2512_ = lean_string_utf8_get(v_inputString_2506_, v_i_2510_);
lean_dec(v_i_2510_);
v___x_2527_ = 65;
v___x_2528_ = lean_uint32_dec_le(v___x_2527_, v_curr_2512_);
if (v___x_2528_ == 0)
{
goto v___jp_2522_;
}
else
{
uint32_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = 90;
v___x_2530_ = lean_uint32_dec_le(v_curr_2512_, v___x_2529_);
if (v___x_2530_ == 0)
{
goto v___jp_2522_;
}
else
{
return v___x_2509_;
}
}
v___jp_2513_:
{
if (v___y_2514_ == 0)
{
uint32_t v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = 171;
v___x_2516_ = lean_uint32_dec_eq(v_curr_2512_, v___x_2515_);
return v___x_2516_;
}
else
{
return v___x_2509_;
}
}
v___jp_2517_:
{
if (v___y_2518_ == 0)
{
uint32_t v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = 95;
v___x_2520_ = lean_uint32_dec_eq(v_curr_2512_, v___x_2519_);
if (v___x_2520_ == 0)
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_isLetterLike(v_curr_2512_);
v___y_2514_ = v___x_2521_;
goto v___jp_2513_;
}
else
{
v___y_2514_ = v___x_2520_;
goto v___jp_2513_;
}
}
else
{
return v___x_2509_;
}
}
v___jp_2522_:
{
uint32_t v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = 97;
v___x_2524_ = lean_uint32_dec_le(v___x_2523_, v_curr_2512_);
if (v___x_2524_ == 0)
{
v___y_2518_ = v___x_2524_;
goto v___jp_2517_;
}
else
{
uint32_t v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = 122;
v___x_2526_ = lean_uint32_dec_le(v_curr_2512_, v___x_2525_);
v___y_2518_ = v___x_2526_;
goto v___jp_2517_;
}
}
}
else
{
uint8_t v___x_2531_; 
lean_dec(v_i_2510_);
v___x_2531_ = 0;
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2532_, lean_object* v_s_2533_){
_start:
{
uint8_t v_res_2534_; lean_object* v_r_2535_; 
v_res_2534_ = l_Lean_Parser_isIdCont(v_c_2532_, v_s_2533_);
lean_dec_ref(v_s_2533_);
lean_dec_ref(v_c_2532_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2536_, lean_object* v_idStopPos_2537_, lean_object* v_tk_2538_){
_start:
{
if (lean_obj_tag(v_tk_2538_) == 0)
{
uint8_t v___x_2539_; 
v___x_2539_ = 0;
return v___x_2539_;
}
else
{
lean_object* v_val_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_val_2540_ = lean_ctor_get(v_tk_2538_, 0);
v___x_2541_ = lean_nat_sub(v_idStopPos_2537_, v_idStartPos_2536_);
v___x_2542_ = lean_string_utf8_byte_size(v_val_2540_);
v___x_2543_ = lean_nat_dec_le(v___x_2541_, v___x_2542_);
lean_dec(v___x_2541_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2544_, lean_object* v_idStopPos_2545_, lean_object* v_tk_2546_){
_start:
{
uint8_t v_res_2547_; lean_object* v_r_2548_; 
v_res_2547_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2544_, v_idStopPos_2545_, v_tk_2546_);
lean_dec(v_tk_2546_);
lean_dec(v_idStopPos_2545_);
lean_dec(v_idStartPos_2544_);
v_r_2548_ = lean_box(v_res_2547_);
return v_r_2548_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 0)
{
if (lean_obj_tag(v_x_2550_) == 0)
{
uint8_t v___x_2551_; 
v___x_2551_ = 1;
return v___x_2551_;
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = 0;
return v___x_2552_;
}
}
else
{
if (lean_obj_tag(v_x_2550_) == 0)
{
uint8_t v___x_2553_; 
v___x_2553_ = 0;
return v___x_2553_;
}
else
{
lean_object* v_val_2554_; lean_object* v_val_2555_; uint8_t v___x_2556_; 
v_val_2554_ = lean_ctor_get(v_x_2549_, 0);
v_val_2555_ = lean_ctor_get(v_x_2550_, 0);
v___x_2556_ = lean_string_dec_eq(v_val_2554_, v_val_2555_);
return v___x_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_x_2557_, v_x_2558_);
lean_dec(v_x_2558_);
lean_dec(v_x_2557_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2563_, lean_object* v_tk_2564_, lean_object* v_c_2565_, lean_object* v_s_2566_){
_start:
{
if (lean_obj_tag(v_tk_2564_) == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec_ref(v_c_2565_);
v___x_2567_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2568_ = lean_box(0);
v___x_2569_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2566_, v___x_2567_, v_startPos_2563_, v___x_2568_);
return v___x_2569_;
}
else
{
lean_object* v_toCacheableParserContext_2570_; lean_object* v_val_2571_; lean_object* v_toInputContext_2572_; lean_object* v_forbiddenTk_x3f_2573_; uint8_t v___x_2574_; 
v_toCacheableParserContext_2570_ = lean_ctor_get(v_c_2565_, 2);
v_val_2571_ = lean_ctor_get(v_tk_2564_, 0);
v_toInputContext_2572_ = lean_ctor_get(v_c_2565_, 0);
lean_inc_ref(v_toInputContext_2572_);
v_forbiddenTk_x3f_2573_ = lean_ctor_get(v_toCacheableParserContext_2570_, 3);
v___x_2574_ = l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTk_x3f_2573_, v_tk_2564_);
if (v___x_2574_ == 0)
{
lean_object* v_leading_2575_; lean_object* v___x_2576_; lean_object* v_stopPos_2577_; lean_object* v_s_2578_; lean_object* v_s_2579_; lean_object* v___y_2581_; lean_object* v_pos_2585_; lean_object* v_inputString_2586_; lean_object* v_endPos_2587_; uint8_t v___x_2588_; 
lean_inc(v_startPos_2563_);
v_leading_2575_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2565_, v_startPos_2563_);
v___x_2576_ = lean_string_utf8_byte_size(v_val_2571_);
v_stopPos_2577_ = lean_nat_add(v_startPos_2563_, v___x_2576_);
lean_inc(v_stopPos_2577_);
v_s_2578_ = l_Lean_Parser_ParserState_setPos(v_s_2566_, v_stopPos_2577_);
v_s_2579_ = l_Lean_Parser_whitespace(v_c_2565_, v_s_2578_);
v_pos_2585_ = lean_ctor_get(v_s_2579_, 2);
lean_inc(v_pos_2585_);
v_inputString_2586_ = lean_ctor_get(v_toInputContext_2572_, 0);
lean_inc_ref(v_inputString_2586_);
v_endPos_2587_ = lean_ctor_get(v_toInputContext_2572_, 3);
lean_inc(v_endPos_2587_);
lean_dec_ref(v_toInputContext_2572_);
v___x_2588_ = lean_nat_dec_le(v_pos_2585_, v_endPos_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; 
lean_dec(v_pos_2585_);
lean_inc(v_stopPos_2577_);
v___x_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2589_, 0, v_inputString_2586_);
lean_ctor_set(v___x_2589_, 1, v_stopPos_2577_);
lean_ctor_set(v___x_2589_, 2, v_endPos_2587_);
v___y_2581_ = v___x_2589_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2590_; 
lean_dec(v_endPos_2587_);
lean_inc(v_stopPos_2577_);
v___x_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2590_, 0, v_inputString_2586_);
lean_ctor_set(v___x_2590_, 1, v_stopPos_2577_);
lean_ctor_set(v___x_2590_, 2, v_pos_2585_);
v___y_2581_ = v___x_2590_;
goto v___jp_2580_;
}
v___jp_2580_:
{
lean_object* v___x_2582_; lean_object* v_atom_2583_; lean_object* v___x_2584_; 
v___x_2582_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2582_, 0, v_leading_2575_);
lean_ctor_set(v___x_2582_, 1, v_startPos_2563_);
lean_ctor_set(v___x_2582_, 2, v___y_2581_);
lean_ctor_set(v___x_2582_, 3, v_stopPos_2577_);
lean_inc(v_val_2571_);
v_atom_2583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2583_, 0, v___x_2582_);
lean_ctor_set(v_atom_2583_, 1, v_val_2571_);
v___x_2584_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2579_, v_atom_2583_);
return v___x_2584_;
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v_toInputContext_2572_);
lean_dec_ref(v_c_2565_);
v___x_2591_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2592_ = lean_box(0);
v___x_2593_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2566_, v___x_2591_, v_startPos_2563_, v___x_2592_);
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2594_, lean_object* v_tk_2595_, lean_object* v_c_2596_, lean_object* v_s_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2594_, v_tk_2595_, v_c_2596_, v_s_2597_);
lean_dec(v_tk_2595_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2599_, lean_object* v_tk_2600_, lean_object* v_val_2601_, uint8_t v_includeWhitespace_2602_, lean_object* v_c_2603_, lean_object* v_s_2604_){
_start:
{
lean_object* v_pos_2605_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; uint8_t v___x_2615_; 
v_pos_2605_ = lean_ctor_get(v_s_2604_, 2);
v___x_2615_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2599_, v_pos_2605_, v_tk_2600_);
if (v___x_2615_ == 0)
{
lean_object* v_toInputContext_2616_; lean_object* v_inputString_2617_; lean_object* v_endPos_2618_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v_pos_2622_; lean_object* v___y_2628_; uint8_t v___x_2631_; 
lean_inc(v_pos_2605_);
v_toInputContext_2616_ = lean_ctor_get(v_c_2603_, 0);
v_inputString_2617_ = lean_ctor_get(v_toInputContext_2616_, 0);
lean_inc_ref(v_inputString_2617_);
v_endPos_2618_ = lean_ctor_get(v_toInputContext_2616_, 3);
lean_inc(v_endPos_2618_);
v___x_2631_ = lean_nat_dec_le(v_pos_2605_, v_endPos_2618_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_inc(v_endPos_2618_);
lean_inc(v_startPos_2599_);
lean_inc_ref(v_inputString_2617_);
v___x_2632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2632_, 0, v_inputString_2617_);
lean_ctor_set(v___x_2632_, 1, v_startPos_2599_);
lean_ctor_set(v___x_2632_, 2, v_endPos_2618_);
v___y_2628_ = v___x_2632_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2633_; 
lean_inc(v_pos_2605_);
lean_inc(v_startPos_2599_);
lean_inc_ref(v_inputString_2617_);
v___x_2633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2633_, 0, v_inputString_2617_);
lean_ctor_set(v___x_2633_, 1, v_startPos_2599_);
lean_ctor_set(v___x_2633_, 2, v_pos_2605_);
v___y_2628_ = v___x_2633_;
goto v___jp_2627_;
}
v___jp_2619_:
{
lean_object* v_leading_2623_; uint8_t v___x_2624_; 
lean_inc(v_startPos_2599_);
v_leading_2623_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2603_, v_startPos_2599_);
lean_dec_ref(v_c_2603_);
v___x_2624_ = lean_nat_dec_le(v_pos_2622_, v_endPos_2618_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
lean_dec(v_pos_2622_);
lean_inc(v_pos_2605_);
v___x_2625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2625_, 0, v_inputString_2617_);
lean_ctor_set(v___x_2625_, 1, v_pos_2605_);
lean_ctor_set(v___x_2625_, 2, v_endPos_2618_);
v___y_2607_ = v___y_2620_;
v___y_2608_ = v___y_2621_;
v___y_2609_ = v_leading_2623_;
v___y_2610_ = v___x_2625_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_endPos_2618_);
lean_inc(v_pos_2605_);
v___x_2626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2626_, 0, v_inputString_2617_);
lean_ctor_set(v___x_2626_, 1, v_pos_2605_);
lean_ctor_set(v___x_2626_, 2, v_pos_2622_);
v___y_2607_ = v___y_2620_;
v___y_2608_ = v___y_2621_;
v___y_2609_ = v_leading_2623_;
v___y_2610_ = v___x_2626_;
goto v___jp_2606_;
}
}
v___jp_2627_:
{
if (v_includeWhitespace_2602_ == 0)
{
lean_inc(v_pos_2605_);
v___y_2620_ = v___y_2628_;
v___y_2621_ = v_s_2604_;
v_pos_2622_ = v_pos_2605_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2629_; lean_object* v_pos_2630_; 
lean_inc_ref(v_c_2603_);
v___x_2629_ = l_Lean_Parser_whitespace(v_c_2603_, v_s_2604_);
v_pos_2630_ = lean_ctor_get(v___x_2629_, 2);
lean_inc(v_pos_2630_);
v___y_2620_ = v___y_2628_;
v___y_2621_ = v___x_2629_;
v_pos_2622_ = v_pos_2630_;
goto v___jp_2619_;
}
}
}
else
{
lean_object* v___x_2634_; 
lean_dec(v_val_2601_);
v___x_2634_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2599_, v_tk_2600_, v_c_2603_, v_s_2604_);
return v___x_2634_;
}
v___jp_2606_:
{
lean_object* v_info_2611_; lean_object* v___x_2612_; lean_object* v_atom_2613_; lean_object* v___x_2614_; 
v_info_2611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2611_, 0, v___y_2609_);
lean_ctor_set(v_info_2611_, 1, v_startPos_2599_);
lean_ctor_set(v_info_2611_, 2, v___y_2610_);
lean_ctor_set(v_info_2611_, 3, v_pos_2605_);
v___x_2612_ = lean_box(0);
v_atom_2613_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2613_, 0, v_info_2611_);
lean_ctor_set(v_atom_2613_, 1, v___y_2607_);
lean_ctor_set(v_atom_2613_, 2, v_val_2601_);
lean_ctor_set(v_atom_2613_, 3, v___x_2612_);
v___x_2614_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2608_, v_atom_2613_);
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2635_, lean_object* v_tk_2636_, lean_object* v_val_2637_, lean_object* v_includeWhitespace_2638_, lean_object* v_c_2639_, lean_object* v_s_2640_){
_start:
{
uint8_t v_includeWhitespace_boxed_2641_; lean_object* v_res_2642_; 
v_includeWhitespace_boxed_2641_ = lean_unbox(v_includeWhitespace_2638_);
v_res_2642_ = l_Lean_Parser_mkIdResult(v_startPos_2635_, v_tk_2636_, v_val_2637_, v_includeWhitespace_boxed_2641_, v_c_2639_, v_s_2640_);
lean_dec(v_tk_2636_);
return v_res_2642_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2643_){
_start:
{
uint8_t v___y_2645_; uint8_t v___y_2657_; uint32_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = 65;
v___x_2668_ = lean_uint32_dec_le(v___x_2667_, v___y_2643_);
if (v___x_2668_ == 0)
{
goto v___jp_2662_;
}
else
{
uint32_t v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = 90;
v___x_2670_ = lean_uint32_dec_le(v___y_2643_, v___x_2669_);
if (v___x_2670_ == 0)
{
goto v___jp_2662_;
}
else
{
return v___x_2670_;
}
}
v___jp_2644_:
{
if (v___y_2645_ == 0)
{
uint32_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = 95;
v___x_2647_ = lean_uint32_dec_eq(v___y_2643_, v___x_2646_);
if (v___x_2647_ == 0)
{
uint32_t v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = 39;
v___x_2649_ = lean_uint32_dec_eq(v___y_2643_, v___x_2648_);
if (v___x_2649_ == 0)
{
uint32_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = 33;
v___x_2651_ = lean_uint32_dec_eq(v___y_2643_, v___x_2650_);
if (v___x_2651_ == 0)
{
uint32_t v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = 63;
v___x_2653_ = lean_uint32_dec_eq(v___y_2643_, v___x_2652_);
if (v___x_2653_ == 0)
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_isLetterLike(v___y_2643_);
if (v___x_2654_ == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Lean_isSubScriptAlnum(v___y_2643_);
return v___x_2655_;
}
else
{
return v___x_2654_;
}
}
else
{
return v___x_2653_;
}
}
else
{
return v___x_2651_;
}
}
else
{
return v___x_2649_;
}
}
else
{
return v___x_2647_;
}
}
else
{
return v___y_2645_;
}
}
v___jp_2656_:
{
if (v___y_2657_ == 0)
{
uint32_t v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = 48;
v___x_2659_ = lean_uint32_dec_le(v___x_2658_, v___y_2643_);
if (v___x_2659_ == 0)
{
v___y_2645_ = v___x_2659_;
goto v___jp_2644_;
}
else
{
uint32_t v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = 57;
v___x_2661_ = lean_uint32_dec_le(v___y_2643_, v___x_2660_);
v___y_2645_ = v___x_2661_;
goto v___jp_2644_;
}
}
else
{
return v___y_2657_;
}
}
v___jp_2662_:
{
uint32_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = 97;
v___x_2664_ = lean_uint32_dec_le(v___x_2663_, v___y_2643_);
if (v___x_2664_ == 0)
{
v___y_2657_ = v___x_2664_;
goto v___jp_2656_;
}
else
{
uint32_t v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = 122;
v___x_2666_ = lean_uint32_dec_le(v___y_2643_, v___x_2665_);
v___y_2657_ = v___x_2666_;
goto v___jp_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2671_){
_start:
{
uint32_t v___y_631__boxed_2672_; uint8_t v_res_2673_; lean_object* v_r_2674_; 
v___y_631__boxed_2672_ = lean_unbox_uint32(v___y_2671_);
lean_dec(v___y_2671_);
v_res_2673_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_631__boxed_2672_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2675_){
_start:
{
uint32_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = 187;
v___x_2677_ = lean_uint32_dec_eq(v___y_2675_, v___x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2678_){
_start:
{
uint32_t v___y_688__boxed_2679_; uint8_t v_res_2680_; lean_object* v_r_2681_; 
v___y_688__boxed_2679_ = lean_unbox_uint32(v___y_2678_);
lean_dec(v___y_2678_);
v_res_2680_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_688__boxed_2679_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2685_, lean_object* v_tk_2686_, uint8_t v_includeWhitespace_2687_, lean_object* v_r_2688_, lean_object* v_c_2689_, lean_object* v_s_2690_){
_start:
{
lean_object* v_pos_2691_; lean_object* v_toInputContext_2692_; uint8_t v___x_2693_; 
v_pos_2691_ = lean_ctor_get(v_s_2690_, 2);
v_toInputContext_2692_ = lean_ctor_get(v_c_2689_, 0);
v___x_2693_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2692_, v_pos_2691_);
if (v___x_2693_ == 0)
{
lean_object* v_inputString_2694_; uint32_t v_curr_2695_; uint32_t v___x_2696_; uint8_t v___x_2697_; 
v_inputString_2694_ = lean_ctor_get(v_toInputContext_2692_, 0);
v_curr_2695_ = lean_string_utf8_get_fast(v_inputString_2694_, v_pos_2691_);
v___x_2696_ = 171;
v___x_2697_ = lean_uint32_dec_eq(v_curr_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___f_2698_; uint8_t v___y_2710_; uint8_t v___y_2713_; uint32_t v___x_2722_; uint8_t v___x_2723_; 
v___f_2698_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2722_ = 65;
v___x_2723_ = lean_uint32_dec_le(v___x_2722_, v_curr_2695_);
if (v___x_2723_ == 0)
{
goto v___jp_2717_;
}
else
{
uint32_t v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = 90;
v___x_2725_ = lean_uint32_dec_le(v_curr_2695_, v___x_2724_);
if (v___x_2725_ == 0)
{
goto v___jp_2717_;
}
else
{
lean_inc(v_pos_2691_);
goto v___jp_2699_;
}
}
v___jp_2699_:
{
lean_object* v___x_2700_; lean_object* v_s_2701_; lean_object* v_pos_2702_; lean_object* v___x_2703_; lean_object* v_r_2704_; uint8_t v___x_2705_; 
v___x_2700_ = l_Lean_Parser_ParserState_next(v_s_2690_, v_c_2689_, v_pos_2691_);
v_s_2701_ = l_Lean_Parser_takeWhileFn(v___f_2698_, v_c_2689_, v___x_2700_);
v_pos_2702_ = lean_ctor_get(v_s_2701_, 2);
lean_inc(v_pos_2702_);
v___x_2703_ = lean_string_utf8_extract(v_inputString_2694_, v_pos_2691_, v_pos_2702_);
lean_dec(v_pos_2691_);
v_r_2704_ = l_Lean_Name_str___override(v_r_2688_, v___x_2703_);
v___x_2705_ = l_Lean_Parser_isIdCont(v_c_2689_, v_s_2701_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; 
lean_dec(v_pos_2702_);
v___x_2706_ = l_Lean_Parser_mkIdResult(v_startPos_2685_, v_tk_2686_, v_r_2704_, v_includeWhitespace_2687_, v_c_2689_, v_s_2701_);
return v___x_2706_;
}
else
{
lean_object* v_s_2707_; 
v_s_2707_ = l_Lean_Parser_ParserState_next(v_s_2701_, v_c_2689_, v_pos_2702_);
lean_dec(v_pos_2702_);
v_r_2688_ = v_r_2704_;
v_s_2690_ = v_s_2707_;
goto _start;
}
}
v___jp_2709_:
{
if (v___y_2710_ == 0)
{
lean_object* v___x_2711_; 
lean_dec(v_r_2688_);
v___x_2711_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2685_, v_tk_2686_, v_c_2689_, v_s_2690_);
return v___x_2711_;
}
else
{
lean_inc(v_pos_2691_);
goto v___jp_2699_;
}
}
v___jp_2712_:
{
if (v___y_2713_ == 0)
{
uint32_t v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = 95;
v___x_2715_ = lean_uint32_dec_eq(v_curr_2695_, v___x_2714_);
if (v___x_2715_ == 0)
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_isLetterLike(v_curr_2695_);
v___y_2710_ = v___x_2716_;
goto v___jp_2709_;
}
else
{
v___y_2710_ = v___x_2715_;
goto v___jp_2709_;
}
}
else
{
lean_inc(v_pos_2691_);
goto v___jp_2699_;
}
}
v___jp_2717_:
{
uint32_t v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = 97;
v___x_2719_ = lean_uint32_dec_le(v___x_2718_, v_curr_2695_);
if (v___x_2719_ == 0)
{
v___y_2713_ = v___x_2719_;
goto v___jp_2712_;
}
else
{
uint32_t v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = 122;
v___x_2721_ = lean_uint32_dec_le(v_curr_2695_, v___x_2720_);
v___y_2713_ = v___x_2721_;
goto v___jp_2712_;
}
}
}
else
{
lean_object* v___f_2726_; lean_object* v_startPart_2727_; lean_object* v___x_2728_; lean_object* v_s_2729_; lean_object* v_pos_2730_; uint8_t v___x_2731_; 
v___f_2726_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2727_ = lean_string_utf8_next_fast(v_inputString_2694_, v_pos_2691_);
v___x_2728_ = l_Lean_Parser_ParserState_setPos(v_s_2690_, v_startPart_2727_);
v_s_2729_ = l_Lean_Parser_takeUntilFn(v___f_2726_, v_c_2689_, v___x_2728_);
v_pos_2730_ = lean_ctor_get(v_s_2729_, 2);
lean_inc(v_pos_2730_);
v___x_2731_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2692_, v_pos_2730_);
if (v___x_2731_ == 0)
{
lean_object* v_s_2732_; lean_object* v___x_2733_; lean_object* v_r_2734_; uint8_t v___x_2735_; 
v_s_2732_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2729_, v_c_2689_, v_pos_2730_);
v___x_2733_ = lean_string_utf8_extract(v_inputString_2694_, v_startPart_2727_, v_pos_2730_);
lean_dec(v_pos_2730_);
v_r_2734_ = l_Lean_Name_str___override(v_r_2688_, v___x_2733_);
v___x_2735_ = l_Lean_Parser_isIdCont(v_c_2689_, v_s_2732_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Parser_mkIdResult(v_startPos_2685_, v_tk_2686_, v_r_2734_, v_includeWhitespace_2687_, v_c_2689_, v_s_2732_);
return v___x_2736_;
}
else
{
lean_object* v_pos_2737_; lean_object* v_s_2738_; 
v_pos_2737_ = lean_ctor_get(v_s_2732_, 2);
lean_inc(v_pos_2737_);
v_s_2738_ = l_Lean_Parser_ParserState_next(v_s_2732_, v_c_2689_, v_pos_2737_);
lean_dec(v_pos_2737_);
v_r_2688_ = v_r_2734_;
v_s_2690_ = v_s_2738_;
goto _start;
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec(v_pos_2730_);
lean_dec_ref(v_c_2689_);
lean_dec(v_r_2688_);
lean_dec(v_startPos_2685_);
v___x_2740_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2741_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2729_, v___x_2740_, v_startPart_2727_);
return v___x_2741_;
}
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec_ref(v_c_2689_);
lean_dec(v_r_2688_);
lean_dec(v_startPos_2685_);
v___x_2742_ = lean_box(0);
v___x_2743_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2690_, v___x_2742_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2744_, lean_object* v_tk_2745_, lean_object* v_includeWhitespace_2746_, lean_object* v_r_2747_, lean_object* v_c_2748_, lean_object* v_s_2749_){
_start:
{
uint8_t v_includeWhitespace_boxed_2750_; lean_object* v_res_2751_; 
v_includeWhitespace_boxed_2750_ = lean_unbox(v_includeWhitespace_2746_);
v_res_2751_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2744_, v_tk_2745_, v_includeWhitespace_boxed_2750_, v_r_2747_, v_c_2748_, v_s_2749_);
lean_dec(v_tk_2745_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2752_, lean_object* v_tk_2753_, lean_object* v_r_2754_, uint8_t v_includeWhitespace_2755_, lean_object* v_c_2756_, lean_object* v_s_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2752_, v_tk_2753_, v_includeWhitespace_2755_, v_r_2754_, v_c_2756_, v_s_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2759_, lean_object* v_tk_2760_, lean_object* v_r_2761_, lean_object* v_includeWhitespace_2762_, lean_object* v_c_2763_, lean_object* v_s_2764_){
_start:
{
uint8_t v_includeWhitespace_boxed_2765_; lean_object* v_res_2766_; 
v_includeWhitespace_boxed_2765_ = lean_unbox(v_includeWhitespace_2762_);
v_res_2766_ = l_Lean_Parser_identFnAux(v_startPos_2759_, v_tk_2760_, v_r_2761_, v_includeWhitespace_boxed_2765_, v_c_2763_, v_s_2764_);
lean_dec(v_tk_2760_);
return v_res_2766_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2767_){
_start:
{
uint8_t v___y_2769_; uint8_t v___y_2773_; uint32_t v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = 65;
v___x_2783_ = lean_uint32_dec_le(v___x_2782_, v_c_2767_);
if (v___x_2783_ == 0)
{
goto v___jp_2777_;
}
else
{
uint32_t v___x_2784_; uint8_t v___x_2785_; 
v___x_2784_ = 90;
v___x_2785_ = lean_uint32_dec_le(v_c_2767_, v___x_2784_);
if (v___x_2785_ == 0)
{
goto v___jp_2777_;
}
else
{
return v___x_2785_;
}
}
v___jp_2768_:
{
if (v___y_2769_ == 0)
{
uint32_t v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = 171;
v___x_2771_ = lean_uint32_dec_eq(v_c_2767_, v___x_2770_);
return v___x_2771_;
}
else
{
return v___y_2769_;
}
}
v___jp_2772_:
{
if (v___y_2773_ == 0)
{
uint32_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = 95;
v___x_2775_ = lean_uint32_dec_eq(v_c_2767_, v___x_2774_);
if (v___x_2775_ == 0)
{
uint8_t v___x_2776_; 
v___x_2776_ = l_Lean_isLetterLike(v_c_2767_);
v___y_2769_ = v___x_2776_;
goto v___jp_2768_;
}
else
{
v___y_2769_ = v___x_2775_;
goto v___jp_2768_;
}
}
else
{
return v___y_2773_;
}
}
v___jp_2777_:
{
uint32_t v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = 97;
v___x_2779_ = lean_uint32_dec_le(v___x_2778_, v_c_2767_);
if (v___x_2779_ == 0)
{
v___y_2773_ = v___x_2779_;
goto v___jp_2772_;
}
else
{
uint32_t v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = 122;
v___x_2781_ = lean_uint32_dec_le(v_c_2767_, v___x_2780_);
v___y_2773_ = v___x_2781_;
goto v___jp_2772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2786_){
_start:
{
uint32_t v_c_boxed_2787_; uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_c_boxed_2787_ = lean_unbox_uint32(v_c_2786_);
lean_dec(v_c_2786_);
v_res_2788_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2787_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2791_, lean_object* v_c_2792_, lean_object* v_s_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v_s_2798_; lean_object* v_stxStack_2799_; lean_object* v_errorMsg_2800_; uint8_t v___x_2801_; 
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_box(0);
v___x_2796_ = 1;
v___x_2797_ = l_Lean_Parser_ParserState_next(v_s_2793_, v_c_2792_, v_startPos_2791_);
v_s_2798_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2791_, v___x_2794_, v___x_2796_, v___x_2795_, v_c_2792_, v___x_2797_);
v_stxStack_2799_ = lean_ctor_get(v_s_2798_, 0);
lean_inc_ref(v_stxStack_2799_);
v_errorMsg_2800_ = lean_ctor_get(v_s_2798_, 4);
lean_inc(v_errorMsg_2800_);
v___x_2801_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2800_, v___x_2794_);
if (v___x_2801_ == 0)
{
lean_dec_ref(v_stxStack_2799_);
return v_s_2798_;
}
else
{
lean_object* v_stx_2802_; 
v_stx_2802_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2799_);
lean_dec_ref(v_stxStack_2799_);
if (lean_obj_tag(v_stx_2802_) == 3)
{
lean_object* v_rawVal_2803_; lean_object* v_info_2804_; lean_object* v_str_2805_; lean_object* v_startPos_2806_; lean_object* v_stopPos_2807_; lean_object* v_s_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_rawVal_2803_ = lean_ctor_get(v_stx_2802_, 1);
lean_inc_ref(v_rawVal_2803_);
v_info_2804_ = lean_ctor_get(v_stx_2802_, 0);
lean_inc(v_info_2804_);
lean_dec_ref(v_stx_2802_);
v_str_2805_ = lean_ctor_get(v_rawVal_2803_, 0);
lean_inc_ref(v_str_2805_);
v_startPos_2806_ = lean_ctor_get(v_rawVal_2803_, 1);
lean_inc(v_startPos_2806_);
v_stopPos_2807_ = lean_ctor_get(v_rawVal_2803_, 2);
lean_inc(v_stopPos_2807_);
lean_dec_ref(v_rawVal_2803_);
v_s_2808_ = l_Lean_Parser_ParserState_popSyntax(v_s_2798_);
v___x_2809_ = lean_string_utf8_extract(v_str_2805_, v_startPos_2806_, v_stopPos_2807_);
lean_dec(v_stopPos_2807_);
lean_dec(v_startPos_2806_);
lean_dec_ref(v_str_2805_);
v___x_2810_ = l_Lean_Syntax_mkNameLit(v___x_2809_, v_info_2804_);
v___x_2811_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2808_, v___x_2810_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec(v_stx_2802_);
v___x_2812_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2813_ = l_Lean_Parser_ParserState_mkError(v_s_2798_, v___x_2812_);
return v___x_2813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2814_, lean_object* v_s_2815_){
_start:
{
lean_object* v_toInputContext_2816_; lean_object* v_pos_2817_; lean_object* v_tokens_2818_; lean_object* v_inputString_2819_; lean_object* v_endPos_2820_; uint32_t v_curr_2821_; uint32_t v___x_2822_; uint8_t v___x_2823_; uint8_t v___x_2824_; uint8_t v___y_2826_; uint8_t v___y_2833_; uint8_t v___y_2840_; uint8_t v___y_2848_; 
v_toInputContext_2816_ = lean_ctor_get(v_c_2814_, 0);
v_pos_2817_ = lean_ctor_get(v_s_2815_, 2);
v_tokens_2818_ = lean_ctor_get(v_c_2814_, 3);
v_inputString_2819_ = lean_ctor_get(v_toInputContext_2816_, 0);
v_endPos_2820_ = lean_ctor_get(v_toInputContext_2816_, 3);
v_curr_2821_ = lean_string_utf8_get(v_inputString_2819_, v_pos_2817_);
v___x_2822_ = 34;
v___x_2823_ = lean_uint32_dec_eq(v_curr_2821_, v___x_2822_);
v___x_2824_ = 1;
if (v___x_2823_ == 0)
{
uint32_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = 39;
v___x_2856_ = lean_uint32_dec_eq(v_curr_2821_, v___x_2855_);
if (v___x_2856_ == 0)
{
v___y_2848_ = v___x_2856_;
goto v___jp_2847_;
}
else
{
lean_object* v___x_2857_; uint32_t v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = lean_string_utf8_next(v_inputString_2819_, v_pos_2817_);
v___x_2858_ = lean_string_utf8_get(v_inputString_2819_, v___x_2857_);
lean_dec(v___x_2857_);
v___x_2859_ = lean_uint32_dec_eq(v___x_2858_, v___x_2855_);
if (v___x_2859_ == 0)
{
v___y_2848_ = v___x_2856_;
goto v___jp_2847_;
}
else
{
v___y_2848_ = v___x_2823_;
goto v___jp_2847_;
}
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_inc(v_pos_2817_);
v___x_2860_ = l_Lean_Parser_ParserState_next(v_s_2815_, v_c_2814_, v_pos_2817_);
v___x_2861_ = l_Lean_Parser_strLitFnAux(v_pos_2817_, v___x_2824_, v_c_2814_, v___x_2860_);
return v___x_2861_;
}
v___jp_2825_:
{
if (v___y_2826_ == 0)
{
lean_object* v_tk_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_inc(v_pos_2817_);
lean_inc_ref(v_tokens_2818_);
v_tk_2827_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2819_, v_tokens_2818_, v_pos_2817_, v_endPos_2820_);
v___x_2828_ = lean_box(0);
v___x_2829_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2817_, v_tk_2827_, v___x_2824_, v___x_2828_, v_c_2814_, v_s_2815_);
lean_dec(v_tk_2827_);
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = l_Lean_Parser_ParserState_next(v_s_2815_, v_c_2814_, v_pos_2817_);
v___x_2831_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2817_, v_c_2814_, v___x_2830_);
return v___x_2831_;
}
}
v___jp_2832_:
{
if (v___y_2833_ == 0)
{
uint32_t v___x_2834_; uint8_t v___x_2835_; 
v___x_2834_ = 114;
v___x_2835_ = lean_uint32_dec_eq(v_curr_2821_, v___x_2834_);
if (v___x_2835_ == 0)
{
v___y_2826_ = v___x_2835_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = lean_string_utf8_next(v_inputString_2819_, v_pos_2817_);
v___x_2837_ = l_Lean_Parser_isRawStrLitStart(v_c_2814_, v___x_2836_);
v___y_2826_ = v___x_2837_;
goto v___jp_2825_;
}
}
else
{
lean_object* v___x_2838_; 
v___x_2838_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2817_, v_c_2814_, v_s_2815_);
return v___x_2838_;
}
}
v___jp_2839_:
{
if (v___y_2840_ == 0)
{
uint32_t v___x_2841_; uint8_t v___x_2842_; 
lean_inc(v_pos_2817_);
v___x_2841_ = 96;
v___x_2842_ = lean_uint32_dec_eq(v_curr_2821_, v___x_2841_);
if (v___x_2842_ == 0)
{
v___y_2833_ = v___x_2842_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2843_; uint32_t v___x_2844_; uint8_t v___x_2845_; 
v___x_2843_ = lean_string_utf8_next(v_inputString_2819_, v_pos_2817_);
v___x_2844_ = lean_string_utf8_get(v_inputString_2819_, v___x_2843_);
lean_dec(v___x_2843_);
v___x_2845_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2844_);
v___y_2833_ = v___x_2845_;
goto v___jp_2832_;
}
}
else
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Parser_numberFnAux(v___x_2824_, v_c_2814_, v_s_2815_);
return v___x_2846_;
}
}
v___jp_2847_:
{
if (v___y_2848_ == 0)
{
uint32_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = 48;
v___x_2850_ = lean_uint32_dec_le(v___x_2849_, v_curr_2821_);
if (v___x_2850_ == 0)
{
v___y_2840_ = v___x_2850_;
goto v___jp_2839_;
}
else
{
uint32_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = 57;
v___x_2852_ = lean_uint32_dec_le(v_curr_2821_, v___x_2851_);
v___y_2840_ = v___x_2852_;
goto v___jp_2839_;
}
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_inc(v_pos_2817_);
v___x_2853_ = l_Lean_Parser_ParserState_next(v_s_2815_, v_c_2814_, v_pos_2817_);
v___x_2854_ = l_Lean_Parser_charLitFnAux(v_pos_2817_, v_c_2814_, v___x_2853_);
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2862_, lean_object* v_s_2863_){
_start:
{
lean_object* v_cache_2864_; lean_object* v_errorMsg_2865_; 
v_cache_2864_ = lean_ctor_get(v_s_2863_, 3);
lean_inc_ref(v_cache_2864_);
v_errorMsg_2865_ = lean_ctor_get(v_s_2863_, 4);
if (lean_obj_tag(v_errorMsg_2865_) == 0)
{
lean_object* v_stxStack_2866_; lean_object* v_lhsPrec_2867_; lean_object* v_pos_2868_; lean_object* v_recoveredErrors_2869_; lean_object* v_parserCache_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2895_; 
v_stxStack_2866_ = lean_ctor_get(v_s_2863_, 0);
v_lhsPrec_2867_ = lean_ctor_get(v_s_2863_, 1);
v_pos_2868_ = lean_ctor_get(v_s_2863_, 2);
v_recoveredErrors_2869_ = lean_ctor_get(v_s_2863_, 5);
v_parserCache_2870_ = lean_ctor_get(v_cache_2864_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_cache_2864_);
if (v_isSharedCheck_2895_ == 0)
{
lean_object* v_unused_2896_; 
v_unused_2896_ = lean_ctor_get(v_cache_2864_, 0);
lean_dec(v_unused_2896_);
v___x_2872_ = v_cache_2864_;
v_isShared_2873_ = v_isSharedCheck_2895_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_parserCache_2870_);
lean_dec(v_cache_2864_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2895_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2874_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2866_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_nat_dec_eq(v___x_2874_, v___x_2875_);
lean_dec(v___x_2874_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2888_; 
lean_inc_ref(v_recoveredErrors_2869_);
lean_inc(v_pos_2868_);
lean_inc(v_lhsPrec_2867_);
lean_inc(v_errorMsg_2865_);
lean_inc_ref(v_stxStack_2866_);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_s_2863_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; lean_object* v_unused_2890_; lean_object* v_unused_2891_; lean_object* v_unused_2892_; lean_object* v_unused_2893_; lean_object* v_unused_2894_; 
v_unused_2889_ = lean_ctor_get(v_s_2863_, 5);
lean_dec(v_unused_2889_);
v_unused_2890_ = lean_ctor_get(v_s_2863_, 4);
lean_dec(v_unused_2890_);
v_unused_2891_ = lean_ctor_get(v_s_2863_, 3);
lean_dec(v_unused_2891_);
v_unused_2892_ = lean_ctor_get(v_s_2863_, 2);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_s_2863_, 1);
lean_dec(v_unused_2893_);
v_unused_2894_ = lean_ctor_get(v_s_2863_, 0);
lean_dec(v_unused_2894_);
v___x_2878_ = v_s_2863_;
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
else
{
lean_dec(v_s_2863_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_tk_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v_tk_2880_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2866_);
lean_inc(v_pos_2868_);
v___x_2881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2881_, 0, v_startPos_2862_);
lean_ctor_set(v___x_2881_, 1, v_pos_2868_);
lean_ctor_set(v___x_2881_, 2, v_tk_2880_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2881_);
v___x_2883_ = v___x_2872_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_parserCache_2870_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 3, v___x_2883_);
v___x_2885_ = v___x_2878_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_stxStack_2866_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_lhsPrec_2867_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_pos_2868_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_errorMsg_2865_);
lean_ctor_set(v_reuseFailAlloc_2886_, 5, v_recoveredErrors_2869_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_del_object(v___x_2872_);
lean_dec_ref(v_parserCache_2870_);
lean_dec(v_startPos_2862_);
return v_s_2863_;
}
}
}
else
{
lean_dec_ref(v_cache_2864_);
lean_dec(v_startPos_2862_);
return v_s_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2897_, lean_object* v_c_2898_, lean_object* v_s_2899_){
_start:
{
lean_object* v_pos_2900_; lean_object* v_cache_2901_; lean_object* v_toInputContext_2902_; uint8_t v___x_2903_; 
v_pos_2900_ = lean_ctor_get(v_s_2899_, 2);
v_cache_2901_ = lean_ctor_get(v_s_2899_, 3);
v_toInputContext_2902_ = lean_ctor_get(v_c_2898_, 0);
v___x_2903_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2902_, v_pos_2900_);
if (v___x_2903_ == 0)
{
lean_object* v_tokenCache_2904_; lean_object* v_startPos_2905_; lean_object* v_stopPos_2906_; lean_object* v_token_2907_; uint8_t v___x_2908_; 
lean_dec(v_expected_2897_);
v_tokenCache_2904_ = lean_ctor_get(v_cache_2901_, 0);
v_startPos_2905_ = lean_ctor_get(v_tokenCache_2904_, 0);
v_stopPos_2906_ = lean_ctor_get(v_tokenCache_2904_, 1);
v_token_2907_ = lean_ctor_get(v_tokenCache_2904_, 2);
v___x_2908_ = lean_nat_dec_eq(v_startPos_2905_, v_pos_2900_);
if (v___x_2908_ == 0)
{
lean_object* v_s_2909_; lean_object* v___x_2910_; 
lean_inc(v_pos_2900_);
v_s_2909_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2898_, v_s_2899_);
v___x_2910_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2900_, v_s_2909_);
return v___x_2910_;
}
else
{
lean_object* v_s_2911_; lean_object* v___x_2912_; 
lean_inc(v_token_2907_);
lean_inc(v_stopPos_2906_);
lean_dec_ref(v_c_2898_);
v_s_2911_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2899_, v_token_2907_);
v___x_2912_ = l_Lean_Parser_ParserState_setPos(v_s_2911_, v_stopPos_2906_);
return v___x_2912_;
}
}
else
{
lean_object* v___x_2913_; 
lean_dec_ref(v_c_2898_);
v___x_2913_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2899_, v_expected_2897_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2914_, lean_object* v_s_2915_){
_start:
{
lean_object* v_pos_2916_; lean_object* v_iniSz_2917_; lean_object* v___x_2918_; lean_object* v_s_2919_; lean_object* v_errorMsg_2920_; 
v_pos_2916_ = lean_ctor_get(v_s_2915_, 2);
lean_inc(v_pos_2916_);
v_iniSz_2917_ = l_Lean_Parser_ParserState_stackSize(v_s_2915_);
v___x_2918_ = lean_box(0);
v_s_2919_ = l_Lean_Parser_tokenFn(v___x_2918_, v_c_2914_, v_s_2915_);
v_errorMsg_2920_ = lean_ctor_get(v_s_2919_, 4);
lean_inc(v_errorMsg_2920_);
if (lean_obj_tag(v_errorMsg_2920_) == 1)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2929_; 
v_isSharedCheck_2929_ = !lean_is_exclusive(v_errorMsg_2920_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v_errorMsg_2920_, 0);
lean_dec(v_unused_2930_);
v___x_2922_ = v_errorMsg_2920_;
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v_errorMsg_2920_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
lean_inc_ref(v_s_2919_);
v___x_2924_ = l_Lean_Parser_ParserState_restore(v_s_2919_, v_iniSz_2917_, v_pos_2916_);
lean_dec(v_iniSz_2917_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 0);
lean_ctor_set(v___x_2922_, 0, v_s_2919_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_s_2919_);
v___x_2926_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2924_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
return v___x_2927_;
}
}
}
else
{
lean_object* v_stxStack_2931_; lean_object* v_stx_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec(v_errorMsg_2920_);
v_stxStack_2931_ = lean_ctor_get(v_s_2919_, 0);
lean_inc_ref(v_stxStack_2931_);
v_stx_2932_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2931_);
lean_dec_ref(v_stxStack_2931_);
v___x_2933_ = l_Lean_Parser_ParserState_restore(v_s_2919_, v_iniSz_2917_, v_pos_2916_);
lean_dec(v_iniSz_2917_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_stx_2932_);
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2933_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2936_, lean_object* v_s_2937_){
_start:
{
lean_object* v_cache_2938_; lean_object* v_tokenCache_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2952_; 
v_cache_2938_ = lean_ctor_get(v_s_2937_, 3);
lean_inc_ref(v_cache_2938_);
v_tokenCache_2939_ = lean_ctor_get(v_cache_2938_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_cache_2938_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_cache_2938_, 1);
lean_dec(v_unused_2953_);
v___x_2941_ = v_cache_2938_;
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_tokenCache_2939_);
lean_dec(v_cache_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_pos_2943_; lean_object* v_startPos_2944_; lean_object* v_token_2945_; uint8_t v___x_2946_; 
v_pos_2943_ = lean_ctor_get(v_s_2937_, 2);
v_startPos_2944_ = lean_ctor_get(v_tokenCache_2939_, 0);
lean_inc(v_startPos_2944_);
v_token_2945_ = lean_ctor_get(v_tokenCache_2939_, 2);
lean_inc(v_token_2945_);
lean_dec_ref(v_tokenCache_2939_);
v___x_2946_ = lean_nat_dec_eq(v_startPos_2944_, v_pos_2943_);
lean_dec(v_startPos_2944_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
lean_dec(v_token_2945_);
lean_del_object(v___x_2941_);
v___x_2947_ = l_Lean_Parser_peekTokenAux(v_c_2936_, v_s_2937_);
return v___x_2947_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_dec_ref(v_c_2936_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_token_2945_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2948_);
lean_ctor_set(v___x_2941_, 0, v_s_2937_);
v___x_2950_ = v___x_2941_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_s_2937_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2954_, lean_object* v_c_2955_, lean_object* v_s_2956_){
_start:
{
lean_object* v_pos_2957_; lean_object* v_toInputContext_2958_; uint8_t v___x_2959_; 
v_pos_2957_ = lean_ctor_get(v_s_2956_, 2);
v_toInputContext_2958_ = lean_ctor_get(v_c_2955_, 0);
v___x_2959_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2958_, v_pos_2957_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_inc(v_pos_2957_);
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_box(0);
v___x_2962_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2957_, v___x_2960_, v_includeWhitespace_2954_, v___x_2961_, v_c_2955_, v_s_2956_);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_dec_ref(v_c_2955_);
v___x_2963_ = lean_box(0);
v___x_2964_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2956_, v___x_2963_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2965_, lean_object* v_c_2966_, lean_object* v_s_2967_){
_start:
{
uint8_t v_includeWhitespace_boxed_2968_; lean_object* v_res_2969_; 
v_includeWhitespace_boxed_2968_ = lean_unbox(v_includeWhitespace_2965_);
v_res_2969_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2968_, v_c_2966_, v_s_2967_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_2970_, lean_object* v_expected_2971_, lean_object* v_c_2972_, lean_object* v_s_2973_){
_start:
{
lean_object* v_pos_2974_; lean_object* v_s_2975_; lean_object* v_stxStack_2976_; lean_object* v_errorMsg_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v_pos_2974_ = lean_ctor_get(v_s_2973_, 2);
lean_inc(v_pos_2974_);
lean_inc(v_expected_2971_);
v_s_2975_ = l_Lean_Parser_tokenFn(v_expected_2971_, v_c_2972_, v_s_2973_);
v_stxStack_2976_ = lean_ctor_get(v_s_2975_, 0);
lean_inc_ref(v_stxStack_2976_);
v_errorMsg_2977_ = lean_ctor_get(v_s_2975_, 4);
lean_inc(v_errorMsg_2977_);
v___x_2978_ = lean_box(0);
v___x_2979_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_dec_ref(v_stxStack_2976_);
lean_dec(v_pos_2974_);
lean_dec(v_expected_2971_);
lean_dec_ref(v_p_2970_);
return v_s_2975_;
}
else
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2976_);
lean_dec_ref(v_stxStack_2976_);
if (lean_obj_tag(v___x_2980_) == 2)
{
lean_object* v_val_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_val_2981_ = lean_ctor_get(v___x_2980_, 1);
lean_inc_ref(v_val_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = lean_apply_1(v_p_2970_, v_val_2981_);
v___x_2983_ = lean_unbox(v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2975_, v_expected_2971_, v_pos_2974_);
return v___x_2984_;
}
else
{
lean_dec(v_pos_2974_);
lean_dec(v_expected_2971_);
return v_s_2975_;
}
}
else
{
lean_object* v___x_2985_; 
lean_dec(v___x_2980_);
lean_dec_ref(v_p_2970_);
v___x_2985_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2975_, v_expected_2971_, v_pos_2974_);
return v___x_2985_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_2986_, lean_object* v_s_2987_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_string_dec_eq(v_s_2987_, v_sym_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_2989_, lean_object* v_s_2990_){
_start:
{
uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_res_2991_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_2989_, v_s_2990_);
lean_dec_ref(v_s_2990_);
lean_dec_ref(v_sym_2989_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_2993_, lean_object* v_errorMsg_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___f_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2997_, 0, v_sym_2993_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_errorMsg_2994_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Lean_Parser_satisfySymbolFn(v___f_2997_, v___x_2999_, v_a_2995_, v_a_2996_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_3001_, lean_object* v_tks_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v_sym_3001_);
lean_ctor_set(v___x_3003_, 1, v_tks_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_3004_){
_start:
{
lean_object* v___f_3005_; lean_object* v___f_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_inc_ref(v_sym_3004_);
v___f_3005_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3005_, 0, v_sym_3004_);
v___f_3006_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_sym_3004_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
v___x_3010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3010_, 0, v___f_3005_);
lean_ctor_set(v___x_3010_, 1, v___f_3006_);
lean_ctor_set(v___x_3010_, 2, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3014_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3015_ = lean_string_append(v___x_3014_, v_sym_3011_);
v___x_3016_ = lean_string_append(v___x_3015_, v___x_3014_);
v___x_3017_ = l_Lean_Parser_symbolFnAux(v_sym_3011_, v___x_3016_, v_a_3012_, v_a_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3018_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v_str_3023_; lean_object* v_startInclusive_3024_; lean_object* v_endExclusive_3025_; lean_object* v_sym_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = lean_string_utf8_byte_size(v_sym_3018_);
v___x_3021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3021_, 0, v_sym_3018_);
lean_ctor_set(v___x_3021_, 1, v___x_3019_);
lean_ctor_set(v___x_3021_, 2, v___x_3020_);
v___x_3022_ = l_String_Slice_trimAscii(v___x_3021_);
v_str_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref(v_str_3023_);
v_startInclusive_3024_ = lean_ctor_get(v___x_3022_, 1);
lean_inc(v_startInclusive_3024_);
v_endExclusive_3025_ = lean_ctor_get(v___x_3022_, 2);
lean_inc(v_endExclusive_3025_);
lean_dec_ref(v___x_3022_);
v_sym_3026_ = lean_string_utf8_extract(v_str_3023_, v_startInclusive_3024_, v_endExclusive_3025_);
lean_dec(v_endExclusive_3025_);
lean_dec(v_startInclusive_3024_);
lean_dec_ref(v_str_3023_);
lean_inc_ref(v_sym_3026_);
v___x_3027_ = l_Lean_Parser_symbolInfo(v_sym_3026_);
v___x_3028_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3028_, 0, v_sym_3026_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Syntax_getTailInfo(v_prev_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_trailing_3032_; lean_object* v_startPos_3033_; lean_object* v_stopPos_3034_; uint8_t v___x_3035_; 
v_trailing_3032_ = lean_ctor_get(v___x_3031_, 2);
lean_inc_ref(v_trailing_3032_);
lean_dec_ref(v___x_3031_);
v_startPos_3033_ = lean_ctor_get(v_trailing_3032_, 1);
lean_inc(v_startPos_3033_);
v_stopPos_3034_ = lean_ctor_get(v_trailing_3032_, 2);
lean_inc(v_stopPos_3034_);
lean_dec_ref(v_trailing_3032_);
v___x_3035_ = lean_nat_dec_eq(v_stopPos_3034_, v_startPos_3033_);
lean_dec(v_startPos_3033_);
lean_dec(v_stopPos_3034_);
return v___x_3035_;
}
else
{
uint8_t v___x_3036_; 
lean_dec(v___x_3031_);
v___x_3036_ = 0;
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3037_){
_start:
{
uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_res_3038_ = l_Lean_Parser_checkTailNoWs(v_prev_3037_);
lean_dec(v_prev_3037_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3040_, lean_object* v_errorMsg_3041_, lean_object* v_c_3042_, lean_object* v_s_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v_s_3046_; lean_object* v_stxStack_3050_; lean_object* v_errorMsg_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3044_ = lean_box(0);
lean_inc_ref(v_errorMsg_3041_);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_errorMsg_3041_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v_s_3046_ = l_Lean_Parser_tokenFn(v___x_3045_, v_c_3042_, v_s_3043_);
v_stxStack_3050_ = lean_ctor_get(v_s_3046_, 0);
lean_inc_ref(v_stxStack_3050_);
v_errorMsg_3051_ = lean_ctor_get(v_s_3046_, 4);
lean_inc(v_errorMsg_3051_);
v___x_3052_ = lean_box(0);
v___x_3053_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_dec_ref(v_stxStack_3050_);
lean_dec_ref(v_errorMsg_3041_);
lean_dec_ref(v_sym_3040_);
return v_s_3046_;
}
else
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3050_);
lean_dec_ref(v_stxStack_3050_);
switch(lean_obj_tag(v___x_3054_))
{
case 2:
{
lean_object* v_val_3055_; uint8_t v___x_3056_; 
v_val_3055_ = lean_ctor_get(v___x_3054_, 1);
lean_inc_ref(v_val_3055_);
lean_dec_ref(v___x_3054_);
v___x_3056_ = lean_string_dec_eq(v_sym_3040_, v_val_3055_);
lean_dec_ref(v_val_3055_);
lean_dec_ref(v_sym_3040_);
if (v___x_3056_ == 0)
{
goto v___jp_3047_;
}
else
{
lean_dec_ref(v_errorMsg_3041_);
return v_s_3046_;
}
}
case 3:
{
lean_object* v_rawVal_3057_; lean_object* v_info_3058_; lean_object* v_str_3059_; lean_object* v_startPos_3060_; lean_object* v_stopPos_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_rawVal_3057_ = lean_ctor_get(v___x_3054_, 1);
lean_inc_ref(v_rawVal_3057_);
v_info_3058_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_info_3058_);
lean_dec_ref(v___x_3054_);
v_str_3059_ = lean_ctor_get(v_rawVal_3057_, 0);
lean_inc_ref(v_str_3059_);
v_startPos_3060_ = lean_ctor_get(v_rawVal_3057_, 1);
lean_inc(v_startPos_3060_);
v_stopPos_3061_ = lean_ctor_get(v_rawVal_3057_, 2);
lean_inc(v_stopPos_3061_);
lean_dec_ref(v_rawVal_3057_);
v___x_3062_ = lean_string_utf8_extract(v_str_3059_, v_startPos_3060_, v_stopPos_3061_);
lean_dec(v_stopPos_3061_);
lean_dec(v_startPos_3060_);
lean_dec_ref(v_str_3059_);
v___x_3063_ = lean_string_dec_eq(v_sym_3040_, v___x_3062_);
lean_dec_ref(v___x_3062_);
if (v___x_3063_ == 0)
{
lean_dec(v_info_3058_);
lean_dec_ref(v_sym_3040_);
goto v___jp_3047_;
}
else
{
lean_object* v_s_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec_ref(v_errorMsg_3041_);
v_s_3064_ = l_Lean_Parser_ParserState_popSyntax(v_s_3046_);
v___x_3065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_info_3058_);
lean_ctor_set(v___x_3065_, 1, v_sym_3040_);
v___x_3066_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3064_, v___x_3065_);
return v___x_3066_;
}
}
default: 
{
lean_dec(v___x_3054_);
lean_dec_ref(v_sym_3040_);
goto v___jp_3047_;
}
}
}
v___jp_3047_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3049_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3046_, v_errorMsg_3041_, v___x_3048_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3071_ = lean_string_append(v___x_3070_, v_sym_3067_);
v___x_3072_ = lean_string_append(v___x_3071_, v___x_3070_);
v___x_3073_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3067_, v___x_3072_, v_a_3068_, v_a_3069_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3078_, uint8_t v_includeIdent_3079_){
_start:
{
lean_object* v___f_3080_; lean_object* v___f_3081_; 
v___f_3080_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3081_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3079_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_sym_3078_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3085_, 0, v___f_3080_);
lean_ctor_set(v___x_3085_, 1, v___f_3081_);
lean_ctor_set(v___x_3085_, 2, v___x_3084_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3086_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3087_, 0, v_sym_3078_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3089_, 0, v___f_3080_);
lean_ctor_set(v___x_3089_, 1, v___f_3081_);
lean_ctor_set(v___x_3089_, 2, v___x_3088_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3090_, lean_object* v_includeIdent_3091_){
_start:
{
uint8_t v_includeIdent_boxed_3092_; lean_object* v_res_3093_; 
v_includeIdent_boxed_3092_ = lean_unbox(v_includeIdent_3091_);
v_res_3093_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3090_, v_includeIdent_boxed_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3094_, uint8_t v_includeIdent_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v_str_3100_; lean_object* v_startInclusive_3101_; lean_object* v_endExclusive_3102_; lean_object* v_sym_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = lean_string_utf8_byte_size(v_sym_3094_);
v___x_3098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3098_, 0, v_sym_3094_);
lean_ctor_set(v___x_3098_, 1, v___x_3096_);
lean_ctor_set(v___x_3098_, 2, v___x_3097_);
v___x_3099_ = l_String_Slice_trimAscii(v___x_3098_);
v_str_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc_ref(v_str_3100_);
v_startInclusive_3101_ = lean_ctor_get(v___x_3099_, 1);
lean_inc(v_startInclusive_3101_);
v_endExclusive_3102_ = lean_ctor_get(v___x_3099_, 2);
lean_inc(v_endExclusive_3102_);
lean_dec_ref(v___x_3099_);
v_sym_3103_ = lean_string_utf8_extract(v_str_3100_, v_startInclusive_3101_, v_endExclusive_3102_);
lean_dec(v_endExclusive_3102_);
lean_dec(v_startInclusive_3101_);
lean_dec_ref(v_str_3100_);
lean_inc_ref(v_sym_3103_);
v___x_3104_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3103_, v_includeIdent_3095_);
v___x_3105_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3105_, 0, v_sym_3103_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3107_, lean_object* v_includeIdent_3108_){
_start:
{
uint8_t v_includeIdent_boxed_3109_; lean_object* v_res_3110_; 
v_includeIdent_boxed_3109_ = lean_unbox(v_includeIdent_3108_);
v_res_3110_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3107_, v_includeIdent_boxed_3109_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3111_, lean_object* v_errorMsg_3112_, lean_object* v_j_3113_, lean_object* v_c_3114_, lean_object* v_s_3115_){
_start:
{
uint8_t v___x_3116_; 
v___x_3116_ = lean_string_utf8_at_end(v_sym_3111_, v_j_3113_);
if (v___x_3116_ == 0)
{
lean_object* v_pos_3117_; lean_object* v_toInputContext_3118_; uint8_t v___x_3119_; 
v_pos_3117_ = lean_ctor_get(v_s_3115_, 2);
v_toInputContext_3118_ = lean_ctor_get(v_c_3114_, 0);
v___x_3119_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3118_, v_pos_3117_);
if (v___x_3119_ == 0)
{
lean_object* v_inputString_3120_; uint32_t v___x_3121_; uint32_t v___x_3122_; uint8_t v___x_3123_; 
v_inputString_3120_ = lean_ctor_get(v_toInputContext_3118_, 0);
v___x_3121_ = lean_string_utf8_get_fast(v_sym_3111_, v_j_3113_);
v___x_3122_ = lean_string_utf8_get_fast(v_inputString_3120_, v_pos_3117_);
v___x_3123_ = lean_uint32_dec_eq(v___x_3121_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; 
lean_dec(v_j_3113_);
v___x_3124_ = l_Lean_Parser_ParserState_mkError(v_s_3115_, v_errorMsg_3112_);
return v___x_3124_;
}
else
{
if (v___x_3119_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_inc(v_pos_3117_);
v___x_3125_ = lean_string_utf8_next_fast(v_sym_3111_, v_j_3113_);
lean_dec(v_j_3113_);
v___x_3126_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3115_, v_c_3114_, v_pos_3117_);
lean_dec(v_pos_3117_);
v_j_3113_ = v___x_3125_;
v_s_3115_ = v___x_3126_;
goto _start;
}
else
{
lean_object* v___x_3128_; 
lean_dec(v_j_3113_);
v___x_3128_ = l_Lean_Parser_ParserState_mkError(v_s_3115_, v_errorMsg_3112_);
return v___x_3128_;
}
}
}
else
{
lean_object* v___x_3129_; 
lean_dec(v_j_3113_);
v___x_3129_ = l_Lean_Parser_ParserState_mkError(v_s_3115_, v_errorMsg_3112_);
return v___x_3129_;
}
}
else
{
lean_dec(v_j_3113_);
lean_dec_ref(v_errorMsg_3112_);
return v_s_3115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3130_, lean_object* v_errorMsg_3131_, lean_object* v_j_3132_, lean_object* v_c_3133_, lean_object* v_s_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3130_, v_errorMsg_3131_, v_j_3132_, v_c_3133_, v_s_3134_);
lean_dec_ref(v_c_3133_);
lean_dec_ref(v_sym_3130_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3136_, lean_object* v_errorMsg_3137_, lean_object* v_j_3138_, lean_object* v_c_3139_, lean_object* v_s_3140_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3136_, v_errorMsg_3137_, v_j_3138_, v_c_3139_, v_s_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3142_, lean_object* v_errorMsg_3143_, lean_object* v_j_3144_, lean_object* v_c_3145_, lean_object* v_s_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Lean_Parser_strAux(v_sym_3142_, v_errorMsg_3143_, v_j_3144_, v_c_3145_, v_s_3146_);
lean_dec_ref(v_c_3145_);
lean_dec_ref(v_sym_3142_);
return v_res_3147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_Syntax_getTailInfo(v_prev_3148_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_trailing_3150_; lean_object* v_startPos_3151_; lean_object* v_stopPos_3152_; uint8_t v___x_3153_; 
v_trailing_3150_ = lean_ctor_get(v___x_3149_, 2);
lean_inc_ref(v_trailing_3150_);
lean_dec_ref(v___x_3149_);
v_startPos_3151_ = lean_ctor_get(v_trailing_3150_, 1);
lean_inc(v_startPos_3151_);
v_stopPos_3152_ = lean_ctor_get(v_trailing_3150_, 2);
lean_inc(v_stopPos_3152_);
lean_dec_ref(v_trailing_3150_);
v___x_3153_ = lean_nat_dec_lt(v_startPos_3151_, v_stopPos_3152_);
lean_dec(v_stopPos_3152_);
lean_dec(v_startPos_3151_);
return v___x_3153_;
}
else
{
uint8_t v___x_3154_; 
lean_dec(v___x_3149_);
v___x_3154_ = 0;
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3155_){
_start:
{
uint8_t v_res_3156_; lean_object* v_r_3157_; 
v_res_3156_ = l_Lean_Parser_checkTailWs(v_prev_3155_);
lean_dec(v_prev_3155_);
v_r_3157_ = lean_box(v_res_3156_);
return v_r_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3158_, lean_object* v_s_3159_){
_start:
{
lean_object* v_stxStack_3160_; lean_object* v_prev_3161_; uint8_t v___x_3162_; 
v_stxStack_3160_ = lean_ctor_get(v_s_3159_, 0);
v_prev_3161_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3160_);
v___x_3162_ = l_Lean_Parser_checkTailWs(v_prev_3161_);
lean_dec(v_prev_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_Parser_ParserState_mkError(v_s_3159_, v_errorMsg_3158_);
return v___x_3163_;
}
else
{
lean_dec_ref(v_errorMsg_3158_);
return v_s_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3164_, lean_object* v_x_3165_, lean_object* v_s_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3164_, v_s_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3168_, lean_object* v_x_3169_, lean_object* v_s_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3168_, v_x_3169_, v_s_3170_);
lean_dec_ref(v_x_3169_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3172_){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3174_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3174_, 0, v_errorMsg_3172_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((lean_object*)(l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3184_ = ((lean_object*)(l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3185_ = l_Lean_addBuiltinDocString(v___x_3183_, v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3188_){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = l_String_instInhabitedSlice;
v___x_3190_ = lean_panic_fn(v___x_3189_, v_msg_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3191_, lean_object* v_a_3192_, uint8_t v_b_3193_){
_start:
{
lean_object* v_str_3194_; lean_object* v_startInclusive_3195_; lean_object* v_endExclusive_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v_str_3194_ = lean_ctor_get(v_s_3191_, 0);
v_startInclusive_3195_ = lean_ctor_get(v_s_3191_, 1);
v_endExclusive_3196_ = lean_ctor_get(v_s_3191_, 2);
v___x_3197_ = lean_nat_sub(v_endExclusive_3196_, v_startInclusive_3195_);
v___x_3198_ = lean_nat_dec_eq(v_a_3192_, v___x_3197_);
lean_dec(v___x_3197_);
if (v___x_3198_ == 0)
{
uint32_t v___x_3199_; lean_object* v___x_3200_; uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3199_ = 10;
v___x_3200_ = lean_nat_add(v_startInclusive_3195_, v_a_3192_);
lean_dec(v_a_3192_);
v___x_3201_ = lean_string_utf8_get_fast(v_str_3194_, v___x_3200_);
v___x_3202_ = lean_uint32_dec_eq(v___x_3201_, v___x_3199_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_string_utf8_next_fast(v_str_3194_, v___x_3200_);
lean_dec(v___x_3200_);
v___x_3204_ = lean_nat_sub(v___x_3203_, v_startInclusive_3195_);
v_a_3192_ = v___x_3204_;
v_b_3193_ = v___x_3202_;
goto _start;
}
else
{
lean_dec(v___x_3200_);
return v___x_3202_;
}
}
else
{
lean_dec(v_a_3192_);
return v_b_3193_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3206_, lean_object* v_a_3207_, lean_object* v_b_3208_){
_start:
{
uint8_t v_b_boxed_3209_; uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_b_boxed_3209_ = lean_unbox(v_b_3208_);
v_res_3210_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3206_, v_a_3207_, v_b_boxed_3209_);
lean_dec_ref(v_s_3206_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3212_){
_start:
{
lean_object* v_searcher_3213_; uint8_t v___x_3214_; uint8_t v___x_3215_; 
v_searcher_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = 0;
v___x_3215_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3212_, v_searcher_3213_, v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3216_){
_start:
{
uint8_t v_res_3217_; lean_object* v_r_3218_; 
v_res_3217_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3216_);
lean_dec_ref(v_s_3216_);
v_r_3218_ = lean_box(v_res_3217_);
return v_r_3218_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3222_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3223_ = lean_unsigned_to_nat(14u);
v___x_3224_ = lean_unsigned_to_nat(22u);
v___x_3225_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3226_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3227_ = l_mkPanicMessageWithDecl(v___x_3226_, v___x_3225_, v___x_3224_, v___x_3223_, v___x_3222_);
return v___x_3227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3228_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Syntax_getTailInfo(v_prev_3228_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_trailing_3234_; lean_object* v_str_3235_; lean_object* v_startPos_3236_; lean_object* v_stopPos_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3248_; 
v_trailing_3234_ = lean_ctor_get(v___x_3233_, 2);
lean_inc_ref(v_trailing_3234_);
lean_dec_ref(v___x_3233_);
v_str_3235_ = lean_ctor_get(v_trailing_3234_, 0);
v_startPos_3236_ = lean_ctor_get(v_trailing_3234_, 1);
v_stopPos_3237_ = lean_ctor_get(v_trailing_3234_, 2);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_trailing_3234_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3239_ = v_trailing_3234_;
v_isShared_3240_ = v_isSharedCheck_3248_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_stopPos_3237_);
lean_inc(v_startPos_3236_);
lean_inc(v_str_3235_);
lean_dec(v_trailing_3234_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3248_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
uint8_t v___x_3241_; 
v___x_3241_ = lean_string_is_valid_pos(v_str_3235_, v_startPos_3236_);
if (v___x_3241_ == 0)
{
lean_del_object(v___x_3239_);
lean_dec(v_stopPos_3237_);
lean_dec(v_startPos_3236_);
lean_dec_ref(v_str_3235_);
goto v___jp_3229_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = lean_string_is_valid_pos(v_str_3235_, v_stopPos_3237_);
if (v___x_3242_ == 0)
{
lean_del_object(v___x_3239_);
lean_dec(v_stopPos_3237_);
lean_dec(v_startPos_3236_);
lean_dec_ref(v_str_3235_);
goto v___jp_3229_;
}
else
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_nat_dec_le(v_startPos_3236_, v_stopPos_3237_);
if (v___x_3243_ == 0)
{
lean_del_object(v___x_3239_);
lean_dec(v_stopPos_3237_);
lean_dec(v_startPos_3236_);
lean_dec_ref(v_str_3235_);
goto v___jp_3229_;
}
else
{
lean_object* v___x_3245_; 
if (v_isShared_3240_ == 0)
{
v___x_3245_ = v___x_3239_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_str_3235_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_startPos_3236_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_stopPos_3237_);
v___x_3245_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
uint8_t v___x_3246_; 
v___x_3246_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3245_);
lean_dec_ref(v___x_3245_);
return v___x_3246_;
}
}
}
}
}
}
else
{
uint8_t v___x_3249_; 
lean_dec(v___x_3233_);
v___x_3249_ = 0;
return v___x_3249_;
}
v___jp_3229_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3230_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3231_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3230_);
v___x_3232_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3231_);
lean_dec_ref(v___x_3231_);
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Lean_Parser_checkTailLinebreak(v_prev_3250_);
lean_dec(v_prev_3250_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3253_, lean_object* v_inst_3254_, lean_object* v_R_3255_, lean_object* v_a_3256_, uint8_t v_b_3257_, lean_object* v_c_3258_){
_start:
{
uint8_t v___x_3259_; 
v___x_3259_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3253_, v_a_3256_, v_b_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3260_, lean_object* v_inst_3261_, lean_object* v_R_3262_, lean_object* v_a_3263_, lean_object* v_b_3264_, lean_object* v_c_3265_){
_start:
{
uint8_t v_b_boxed_3266_; uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_b_boxed_3266_ = lean_unbox(v_b_3264_);
v_res_3267_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3260_, v_inst_3261_, v_R_3262_, v_a_3263_, v_b_boxed_3266_, v_c_3265_);
lean_dec_ref(v_s_3260_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3269_, lean_object* v_s_3270_){
_start:
{
lean_object* v_stxStack_3271_; lean_object* v_prev_3272_; uint8_t v___x_3273_; 
v_stxStack_3271_ = lean_ctor_get(v_s_3270_, 0);
v_prev_3272_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3271_);
v___x_3273_ = l_Lean_Parser_checkTailLinebreak(v_prev_3272_);
lean_dec(v_prev_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Parser_ParserState_mkError(v_s_3270_, v_errorMsg_3269_);
return v___x_3274_;
}
else
{
lean_dec_ref(v_errorMsg_3269_);
return v_s_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3275_, lean_object* v_x_3276_, lean_object* v_s_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3275_, v_s_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3279_, lean_object* v_x_3280_, lean_object* v_s_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3279_, v_x_3280_, v_s_3281_);
lean_dec_ref(v_x_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3283_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3285_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3285_, 0, v_errorMsg_3283_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = ((lean_object*)(l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3295_ = ((lean_object*)(l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3296_ = l_Lean_addBuiltinDocString(v___x_3294_, v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3299_, lean_object* v_i_3300_){
_start:
{
lean_object* v_zero_3301_; uint8_t v_isZero_3302_; 
v_zero_3301_ = lean_unsigned_to_nat(0u);
v_isZero_3302_ = lean_nat_dec_eq(v_i_3300_, v_zero_3301_);
if (v_isZero_3302_ == 1)
{
lean_object* v___x_3303_; 
lean_dec(v_i_3300_);
v___x_3303_ = lean_box(0);
return v___x_3303_;
}
else
{
lean_object* v_one_3304_; lean_object* v_n_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v_one_3304_ = lean_unsigned_to_nat(1u);
v_n_3305_ = lean_nat_sub(v_i_3300_, v_one_3304_);
lean_dec(v_i_3300_);
v___x_3306_ = l_Subarray_get___redArg(v_as_3299_, v_n_3305_);
v___x_3307_ = l_Lean_Syntax_isNone(v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_dec(v_n_3305_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
return v___x_3308_;
}
else
{
lean_dec(v___x_3306_);
v_i_3300_ = v_n_3305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3310_, lean_object* v_i_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3310_, v_i_3311_);
lean_dec_ref(v_as_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3313_){
_start:
{
lean_object* v___x_3314_; lean_object* v_start_3315_; lean_object* v_stop_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3314_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3313_);
v_start_3315_ = lean_ctor_get(v___x_3314_, 1);
lean_inc(v_start_3315_);
v_stop_3316_ = lean_ctor_get(v___x_3314_, 2);
lean_inc(v_stop_3316_);
v___x_3317_ = lean_nat_sub(v_stop_3316_, v_start_3315_);
lean_dec(v_start_3315_);
lean_dec(v_stop_3316_);
v___x_3318_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3314_, v___x_3317_);
lean_dec_ref(v___x_3314_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_box(0);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; 
v_val_3320_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3320_);
lean_dec_ref(v___x_3318_);
return v_val_3320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3321_, lean_object* v_i_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3321_, v_i_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3325_, lean_object* v_i_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3325_, v_i_3326_, v_a_3327_);
lean_dec_ref(v_as_3325_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3329_, lean_object* v_s_3330_){
_start:
{
lean_object* v_stxStack_3331_; lean_object* v_prev_3332_; uint8_t v___x_3333_; 
v_stxStack_3331_ = lean_ctor_get(v_s_3330_, 0);
lean_inc_ref(v_stxStack_3331_);
v_prev_3332_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3331_);
v___x_3333_ = l_Lean_Parser_checkTailNoWs(v_prev_3332_);
lean_dec(v_prev_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_Parser_ParserState_mkError(v_s_3330_, v_errorMsg_3329_);
return v___x_3334_;
}
else
{
lean_dec_ref(v_errorMsg_3329_);
return v_s_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3335_, lean_object* v_x_3336_, lean_object* v_s_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3335_, v_s_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3339_, lean_object* v_x_3340_, lean_object* v_s_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3339_, v_x_3340_, v_s_3341_);
lean_dec_ref(v_x_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3345_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3345_, 0, v_errorMsg_3343_);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = ((lean_object*)(l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3355_ = ((lean_object*)(l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3356_ = l_Lean_addBuiltinDocString(v___x_3354_, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3359_, lean_object* v_asciiSym_3360_, lean_object* v_s_3361_){
_start:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_string_dec_eq(v_s_3361_, v_sym_3359_);
if (v___x_3362_ == 0)
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_string_dec_eq(v_s_3361_, v_asciiSym_3360_);
return v___x_3363_;
}
else
{
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3364_, lean_object* v_asciiSym_3365_, lean_object* v_s_3366_){
_start:
{
uint8_t v_res_3367_; lean_object* v_r_3368_; 
v_res_3367_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3364_, v_asciiSym_3365_, v_s_3366_);
lean_dec_ref(v_s_3366_);
lean_dec_ref(v_asciiSym_3365_);
lean_dec_ref(v_sym_3364_);
v_r_3368_ = lean_box(v_res_3367_);
return v_r_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3369_, lean_object* v_asciiSym_3370_, lean_object* v_expected_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___f_3374_; lean_object* v___x_3375_; 
v___f_3374_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3374_, 0, v_sym_3369_);
lean_closure_set(v___f_3374_, 1, v_asciiSym_3370_);
v___x_3375_ = l_Lean_Parser_satisfySymbolFn(v___f_3374_, v_expected_3371_, v_a_3372_, v_a_3373_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3376_, lean_object* v_sym_3377_, lean_object* v_tks_3378_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_asciiSym_3376_);
lean_ctor_set(v___x_3379_, 1, v_tks_3378_);
v___x_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_sym_3377_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3381_, lean_object* v_asciiSym_3382_){
_start:
{
lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_inc_ref(v_sym_3381_);
lean_inc_ref(v_asciiSym_3382_);
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3383_, 0, v_asciiSym_3382_);
lean_closure_set(v___f_3383_, 1, v_sym_3381_);
v___f_3384_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_asciiSym_3382_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_sym_3381_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3389_, 0, v___f_3383_);
lean_ctor_set(v___x_3389_, 1, v___f_3384_);
lean_ctor_set(v___x_3389_, 2, v___x_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3391_, lean_object* v_asciiSym_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3395_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3396_ = lean_string_append(v___x_3395_, v_sym_3391_);
v___x_3397_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3398_ = lean_string_append(v___x_3396_, v___x_3397_);
v___x_3399_ = lean_string_append(v___x_3398_, v_asciiSym_3392_);
v___x_3400_ = lean_string_append(v___x_3399_, v___x_3395_);
v___x_3401_ = lean_box(0);
v___x_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3400_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3391_, v_asciiSym_3392_, v___x_3402_, v_a_3393_, v_a_3394_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3404_, lean_object* v_asciiSym_3405_){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v_str_3410_; lean_object* v_startInclusive_3411_; lean_object* v_endExclusive_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3429_; 
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = lean_string_utf8_byte_size(v_sym_3404_);
v___x_3408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3408_, 0, v_sym_3404_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
lean_ctor_set(v___x_3408_, 2, v___x_3407_);
v___x_3409_ = l_String_Slice_trimAscii(v___x_3408_);
v_str_3410_ = lean_ctor_get(v___x_3409_, 0);
v_startInclusive_3411_ = lean_ctor_get(v___x_3409_, 1);
v_endExclusive_3412_ = lean_ctor_get(v___x_3409_, 2);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3414_ = v___x_3409_;
v_isShared_3415_ = v_isSharedCheck_3429_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_endExclusive_3412_);
lean_inc(v_startInclusive_3411_);
lean_inc(v_str_3410_);
lean_dec(v___x_3409_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3429_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_string_utf8_byte_size(v_asciiSym_3405_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 2, v___x_3416_);
lean_ctor_set(v___x_3414_, 1, v___x_3406_);
lean_ctor_set(v___x_3414_, 0, v_asciiSym_3405_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_asciiSym_3405_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; lean_object* v_str_3420_; lean_object* v_startInclusive_3421_; lean_object* v_endExclusive_3422_; lean_object* v_sym_3423_; lean_object* v_asciiSym_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3419_ = l_String_Slice_trimAscii(v___x_3418_);
v_str_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc_ref(v_str_3420_);
v_startInclusive_3421_ = lean_ctor_get(v___x_3419_, 1);
lean_inc(v_startInclusive_3421_);
v_endExclusive_3422_ = lean_ctor_get(v___x_3419_, 2);
lean_inc(v_endExclusive_3422_);
lean_dec_ref(v___x_3419_);
v_sym_3423_ = lean_string_utf8_extract(v_str_3410_, v_startInclusive_3411_, v_endExclusive_3412_);
lean_dec(v_endExclusive_3412_);
lean_dec(v_startInclusive_3411_);
lean_dec_ref(v_str_3410_);
v_asciiSym_3424_ = lean_string_utf8_extract(v_str_3420_, v_startInclusive_3421_, v_endExclusive_3422_);
lean_dec(v_endExclusive_3422_);
lean_dec(v_startInclusive_3421_);
lean_dec_ref(v_str_3420_);
lean_inc_ref(v_asciiSym_3424_);
lean_inc_ref(v_sym_3423_);
v___x_3425_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3423_, v_asciiSym_3424_);
v___x_3426_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3426_, 0, v_sym_3423_);
lean_closure_set(v___x_3426_, 1, v_asciiSym_3424_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
return v___x_3427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3430_, lean_object* v_asciiSym_3431_, uint8_t v_preserveForPP_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3430_, v_asciiSym_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3434_, lean_object* v_asciiSym_3435_, lean_object* v_preserveForPP_3436_){
_start:
{
uint8_t v_preserveForPP_boxed_3437_; lean_object* v_res_3438_; 
v_preserveForPP_boxed_3437_ = lean_unbox(v_preserveForPP_3436_);
v_res_3438_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3434_, v_asciiSym_3435_, v_preserveForPP_boxed_3437_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3439_){
_start:
{
lean_object* v___f_3440_; lean_object* v___f_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___f_3440_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3441_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3443_, 0, v_k_3439_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
v___x_3445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3445_, 0, v___f_3440_);
lean_ctor_set(v___x_3445_, 1, v___f_3441_);
lean_ctor_set(v___x_3445_, 2, v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3446_, lean_object* v_desc_3447_, lean_object* v_c_3448_, lean_object* v_s_3449_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v_s_3452_; lean_object* v_stxStack_3453_; lean_object* v_errorMsg_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3450_ = lean_box(0);
lean_inc_ref(v_desc_3447_);
v___x_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3451_, 0, v_desc_3447_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v_s_3452_ = l_Lean_Parser_tokenFn(v___x_3451_, v_c_3448_, v_s_3449_);
v_stxStack_3453_ = lean_ctor_get(v_s_3452_, 0);
lean_inc_ref(v_stxStack_3453_);
v_errorMsg_3454_ = lean_ctor_get(v_s_3452_, 4);
lean_inc(v_errorMsg_3454_);
v___x_3455_ = lean_box(0);
v___x_3456_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_dec_ref(v_stxStack_3453_);
lean_dec_ref(v_desc_3447_);
return v_s_3452_;
}
else
{
lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3453_);
lean_dec_ref(v_stxStack_3453_);
v___x_3458_ = l_Lean_Syntax_isOfKind(v___x_3457_, v_k_3446_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_unsigned_to_nat(0u);
v___x_3460_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3452_, v_desc_3447_, v___x_3459_);
return v___x_3460_;
}
else
{
lean_dec_ref(v_desc_3447_);
return v_s_3452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3461_, lean_object* v_desc_3462_, lean_object* v_c_3463_, lean_object* v_s_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Parser_expectTokenFn(v_k_3461_, v_desc_3462_, v_c_3463_, v_s_3464_);
lean_dec(v_k_3461_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3469_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3470_ = l_Lean_Parser_expectTokenFn(v___x_3468_, v___x_3469_, v_a_3466_, v_a_3467_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3472_ = l_Lean_Parser_mkAtomicInfo(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3474_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3480_, lean_object* v_s_3481_){
_start:
{
lean_object* v_pos_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_pos_3482_ = lean_ctor_get(v_s_3481_, 2);
lean_inc(v_pos_3482_);
v___x_3483_ = 1;
v___x_3484_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3485_ = l_Lean_Parser_hexNumberFn(v_pos_3482_, v___x_3483_, v___x_3484_, v_ctx_3480_, v_s_3481_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3487_ = l_Lean_Parser_mkAtomicInfo(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3489_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3488_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3496_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3497_ = l_Lean_Parser_expectTokenFn(v___x_3495_, v___x_3496_, v_a_3493_, v_a_3494_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3499_ = l_Lean_Parser_mkAtomicInfo(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3501_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3500_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3508_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3509_ = l_Lean_Parser_expectTokenFn(v___x_3507_, v___x_3508_, v_a_3505_, v_a_3506_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3511_ = l_Lean_Parser_mkAtomicInfo(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3513_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3520_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3521_ = l_Lean_Parser_expectTokenFn(v___x_3519_, v___x_3520_, v_a_3517_, v_a_3518_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3523_ = l_Lean_Parser_mkAtomicInfo(v___x_3522_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3525_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v___x_3524_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3535_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3536_ = l_Lean_Parser_expectTokenFn(v___x_3534_, v___x_3535_, v_a_3532_, v_a_3533_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3538_ = l_Lean_Parser_mkAtomicInfo(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3540_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3549_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3550_ = l_Lean_Parser_expectTokenFn(v___x_3548_, v___x_3549_, v_a_3546_, v_a_3547_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3552_ = l_Lean_Parser_mkAtomicInfo(v___x_3551_);
return v___x_3552_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3554_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___x_3553_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3568_, lean_object* v_c_3569_, lean_object* v_s_3570_){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v_s_3573_; lean_object* v_stxStack_3574_; lean_object* v_errorMsg_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3571_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3572_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3573_ = l_Lean_Parser_tokenFn(v___x_3572_, v_c_3569_, v_s_3570_);
v_stxStack_3574_ = lean_ctor_get(v_s_3573_, 0);
lean_inc_ref(v_stxStack_3574_);
v_errorMsg_3575_ = lean_ctor_get(v_s_3573_, 4);
lean_inc(v_errorMsg_3575_);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v_stxStack_3574_);
lean_dec(v_id_3568_);
return v_s_3573_;
}
else
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3574_);
lean_dec_ref(v_stxStack_3574_);
if (lean_obj_tag(v___x_3578_) == 3)
{
lean_object* v_val_3579_; uint8_t v___x_3580_; 
v_val_3579_ = lean_ctor_get(v___x_3578_, 2);
lean_inc(v_val_3579_);
lean_dec_ref(v___x_3578_);
v___x_3580_ = lean_name_eq(v_val_3579_, v_id_3568_);
lean_dec(v_val_3579_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3581_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3582_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3568_, v___x_3577_);
v___x_3583_ = lean_string_append(v___x_3581_, v___x_3582_);
lean_dec_ref(v___x_3582_);
v___x_3584_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3585_ = lean_string_append(v___x_3583_, v___x_3584_);
v___x_3586_ = lean_unsigned_to_nat(0u);
v___x_3587_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3573_, v___x_3585_, v___x_3586_);
return v___x_3587_;
}
else
{
lean_dec(v_id_3568_);
return v_s_3573_;
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec(v___x_3578_);
lean_dec(v_id_3568_);
v___x_3588_ = lean_unsigned_to_nat(0u);
v___x_3589_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3573_, v___x_3571_, v___x_3588_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3592_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3592_, 0, v_id_3590_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3597_, lean_object* v_s_3598_){
_start:
{
lean_object* v_pos_3600_; lean_object* v_str_3601_; lean_object* v_trailing_3602_; lean_object* v_s_3603_; lean_object* v_stxStack_3615_; lean_object* v_pos_3616_; uint8_t v___x_3619_; 
v_stxStack_3615_ = lean_ctor_get(v_s_3598_, 0);
v_pos_3616_ = lean_ctor_get(v_s_3598_, 2);
v___x_3619_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3615_);
if (v___x_3619_ == 0)
{
lean_object* v_prev_3620_; lean_object* v___x_3621_; 
v_prev_3620_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3615_);
v___x_3621_ = l_Lean_Syntax_getTailInfo(v_prev_3620_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_leading_3622_; lean_object* v_pos_3623_; lean_object* v_trailing_3624_; lean_object* v_endPos_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3636_; 
v_leading_3622_ = lean_ctor_get(v___x_3621_, 0);
v_pos_3623_ = lean_ctor_get(v___x_3621_, 1);
v_trailing_3624_ = lean_ctor_get(v___x_3621_, 2);
v_endPos_3625_ = lean_ctor_get(v___x_3621_, 3);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3627_ = v___x_3621_;
v_isShared_3628_ = v_isSharedCheck_3636_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_endPos_3625_);
lean_inc(v_trailing_3624_);
lean_inc(v_pos_3623_);
lean_inc(v_leading_3622_);
lean_dec(v___x_3621_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3636_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_str_3629_; lean_object* v___x_3630_; lean_object* v___x_3632_; 
lean_inc(v_endPos_3625_);
v_str_3629_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3597_, v_endPos_3625_);
v___x_3630_ = l_Lean_Parser_ParserState_popSyntax(v_s_3598_);
lean_inc(v_endPos_3625_);
lean_inc_ref(v_str_3629_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 2, v_str_3629_);
v___x_3632_ = v___x_3627_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_leading_3622_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_pos_3623_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_str_3629_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_endPos_3625_);
v___x_3632_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v_s_3634_; 
v___x_3633_ = l_Lean_Syntax_setTailInfo(v_prev_3620_, v___x_3632_);
v_s_3634_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3630_, v___x_3633_);
v_pos_3600_ = v_endPos_3625_;
v_str_3601_ = v_str_3629_;
v_trailing_3602_ = v_trailing_3624_;
v_s_3603_ = v_s_3634_;
goto v___jp_3599_;
}
}
}
else
{
lean_inc(v_pos_3616_);
lean_dec(v___x_3621_);
lean_dec(v_prev_3620_);
goto v___jp_3617_;
}
}
else
{
lean_inc(v_pos_3616_);
goto v___jp_3617_;
}
v___jp_3599_:
{
lean_object* v_info_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_ident_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_inc(v_pos_3600_);
lean_inc_ref(v_str_3601_);
v_info_3604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3604_, 0, v_str_3601_);
lean_ctor_set(v_info_3604_, 1, v_pos_3600_);
lean_ctor_set(v_info_3604_, 2, v_trailing_3602_);
lean_ctor_set(v_info_3604_, 3, v_pos_3600_);
v___x_3605_ = lean_box(0);
v___x_3606_ = lean_box(0);
v_ident_3607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3607_, 0, v_info_3604_);
lean_ctor_set(v_ident_3607_, 1, v_str_3601_);
lean_ctor_set(v_ident_3607_, 2, v___x_3605_);
lean_ctor_set(v_ident_3607_, 3, v___x_3606_);
v___x_3608_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3609_ = lean_unsigned_to_nat(1u);
v___x_3610_ = lean_mk_empty_array_with_capacity(v___x_3609_);
v___x_3611_ = lean_array_push(v___x_3610_, v_ident_3607_);
v___x_3612_ = lean_box(2);
v___x_3613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___x_3608_);
lean_ctor_set(v___x_3613_, 2, v___x_3611_);
v___x_3614_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3603_, v___x_3613_);
return v___x_3614_;
}
v___jp_3617_:
{
lean_object* v_str_3618_; 
lean_inc(v_pos_3616_);
v_str_3618_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3597_, v_pos_3616_);
lean_inc_ref(v_str_3618_);
v_pos_3600_ = v_pos_3616_;
v_str_3601_ = v_str_3618_;
v_trailing_3602_ = v_str_3618_;
v_s_3603_ = v_s_3598_;
goto v___jp_3599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3637_, lean_object* v_s_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_Parser_hygieneInfoFn(v_c_3637_, v_s_3638_);
lean_dec_ref(v_c_3637_);
return v_res_3639_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3641_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3642_ = l_Lean_Parser_nodeInfo(v___x_3641_, v___x_3640_);
return v___x_3642_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3644_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v___x_3643_);
return v___x_3645_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3647_, lean_object* v_startStackSize_3648_){
_start:
{
lean_object* v_node_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_node_3649_ = l_Lean_Parser_SyntaxStack_back(v_s_3647_);
v___x_3650_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3647_, v_startStackSize_3648_);
v___x_3651_ = l_Lean_Parser_SyntaxStack_push(v___x_3650_, v_node_3649_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3652_, lean_object* v_startStackSize_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Parser_ParserState_keepTop(v_s_3652_, v_startStackSize_3653_);
lean_dec(v_startStackSize_3653_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3655_, lean_object* v_oldStackSize_3656_){
_start:
{
lean_object* v_stxStack_3657_; lean_object* v_lhsPrec_3658_; lean_object* v_pos_3659_; lean_object* v_cache_3660_; lean_object* v_errorMsg_3661_; lean_object* v_recoveredErrors_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3670_; 
v_stxStack_3657_ = lean_ctor_get(v_s_3655_, 0);
v_lhsPrec_3658_ = lean_ctor_get(v_s_3655_, 1);
v_pos_3659_ = lean_ctor_get(v_s_3655_, 2);
v_cache_3660_ = lean_ctor_get(v_s_3655_, 3);
v_errorMsg_3661_ = lean_ctor_get(v_s_3655_, 4);
v_recoveredErrors_3662_ = lean_ctor_get(v_s_3655_, 5);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_s_3655_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3664_ = v_s_3655_;
v_isShared_3665_ = v_isSharedCheck_3670_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_recoveredErrors_3662_);
lean_inc(v_errorMsg_3661_);
lean_inc(v_cache_3660_);
lean_inc(v_pos_3659_);
lean_inc(v_lhsPrec_3658_);
lean_inc(v_stxStack_3657_);
lean_dec(v_s_3655_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3670_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3666_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3657_, v_oldStackSize_3656_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3666_);
v___x_3668_ = v___x_3664_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_lhsPrec_3658_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_pos_3659_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_cache_3660_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_errorMsg_3661_);
lean_ctor_set(v_reuseFailAlloc_3669_, 5, v_recoveredErrors_3662_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3671_, lean_object* v_oldStackSize_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Parser_ParserState_keepNewError(v_s_3671_, v_oldStackSize_3672_);
lean_dec(v_oldStackSize_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3674_, lean_object* v_oldStackSize_3675_, lean_object* v_oldStopPos_3676_, lean_object* v_oldError_3677_, lean_object* v_oldLhsPrec_3678_){
_start:
{
lean_object* v_stxStack_3679_; lean_object* v_cache_3680_; lean_object* v_recoveredErrors_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3689_; 
v_stxStack_3679_ = lean_ctor_get(v_s_3674_, 0);
v_cache_3680_ = lean_ctor_get(v_s_3674_, 3);
v_recoveredErrors_3681_ = lean_ctor_get(v_s_3674_, 5);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_s_3674_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; 
v_unused_3690_ = lean_ctor_get(v_s_3674_, 4);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_s_3674_, 2);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_s_3674_, 1);
lean_dec(v_unused_3692_);
v___x_3683_ = v_s_3674_;
v_isShared_3684_ = v_isSharedCheck_3689_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_recoveredErrors_3681_);
lean_inc(v_cache_3680_);
lean_inc(v_stxStack_3679_);
lean_dec(v_s_3674_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3689_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3685_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3679_, v_oldStackSize_3675_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v_oldError_3677_);
lean_ctor_set(v___x_3683_, 2, v_oldStopPos_3676_);
lean_ctor_set(v___x_3683_, 1, v_oldLhsPrec_3678_);
lean_ctor_set(v___x_3683_, 0, v___x_3685_);
v___x_3687_ = v___x_3683_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_oldLhsPrec_3678_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_oldStopPos_3676_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_cache_3680_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_oldError_3677_);
lean_ctor_set(v_reuseFailAlloc_3688_, 5, v_recoveredErrors_3681_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3693_, lean_object* v_oldStackSize_3694_, lean_object* v_oldStopPos_3695_, lean_object* v_oldError_3696_, lean_object* v_oldLhsPrec_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3693_, v_oldStackSize_3694_, v_oldStopPos_3695_, v_oldError_3696_, v_oldLhsPrec_3697_);
lean_dec(v_oldStackSize_3694_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3699_, lean_object* v_oldStackSize_3700_, lean_object* v_oldError_3701_){
_start:
{
lean_object* v_stxStack_3702_; lean_object* v_lhsPrec_3703_; lean_object* v_pos_3704_; lean_object* v_cache_3705_; lean_object* v_errorMsg_3706_; lean_object* v_recoveredErrors_3707_; lean_object* v___y_3709_; 
v_stxStack_3702_ = lean_ctor_get(v_s_3699_, 0);
v_lhsPrec_3703_ = lean_ctor_get(v_s_3699_, 1);
v_pos_3704_ = lean_ctor_get(v_s_3699_, 2);
v_cache_3705_ = lean_ctor_get(v_s_3699_, 3);
v_errorMsg_3706_ = lean_ctor_get(v_s_3699_, 4);
v_recoveredErrors_3707_ = lean_ctor_get(v_s_3699_, 5);
if (lean_obj_tag(v_errorMsg_3706_) == 1)
{
lean_object* v_val_3713_; uint8_t v___x_3714_; 
lean_inc_ref(v_errorMsg_3706_);
lean_inc_ref(v_recoveredErrors_3707_);
lean_inc_ref(v_cache_3705_);
lean_inc(v_pos_3704_);
lean_inc(v_lhsPrec_3703_);
lean_inc_ref(v_stxStack_3702_);
lean_dec_ref(v_s_3699_);
v_val_3713_ = lean_ctor_get(v_errorMsg_3706_, 0);
lean_inc(v_val_3713_);
lean_dec_ref(v_errorMsg_3706_);
lean_inc(v_val_3713_);
lean_inc_ref(v_oldError_3701_);
v___x_3714_ = l_Lean_Parser_instBEqError_beq(v_oldError_3701_, v_val_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Parser_Error_merge(v_oldError_3701_, v_val_3713_);
v___y_3709_ = v___x_3715_;
goto v___jp_3708_;
}
else
{
lean_dec_ref(v_oldError_3701_);
v___y_3709_ = v_val_3713_;
goto v___jp_3708_;
}
}
else
{
lean_dec_ref(v_oldError_3701_);
return v_s_3699_;
}
v___jp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3710_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3702_, v_oldStackSize_3700_);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___y_3709_);
v___x_3712_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v_lhsPrec_3703_);
lean_ctor_set(v___x_3712_, 2, v_pos_3704_);
lean_ctor_set(v___x_3712_, 3, v_cache_3705_);
lean_ctor_set(v___x_3712_, 4, v___x_3711_);
lean_ctor_set(v___x_3712_, 5, v_recoveredErrors_3707_);
return v___x_3712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3716_, lean_object* v_oldStackSize_3717_, lean_object* v_oldError_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3716_, v_oldStackSize_3717_, v_oldError_3718_);
lean_dec(v_oldStackSize_3717_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3720_, lean_object* v_startStackSize_3721_){
_start:
{
lean_object* v_stxStack_3722_; lean_object* v_lhsPrec_3723_; lean_object* v_pos_3724_; lean_object* v_cache_3725_; lean_object* v_recoveredErrors_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3735_; 
v_stxStack_3722_ = lean_ctor_get(v_s_3720_, 0);
v_lhsPrec_3723_ = lean_ctor_get(v_s_3720_, 1);
v_pos_3724_ = lean_ctor_get(v_s_3720_, 2);
v_cache_3725_ = lean_ctor_get(v_s_3720_, 3);
v_recoveredErrors_3726_ = lean_ctor_get(v_s_3720_, 5);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_s_3720_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v_s_3720_, 4);
lean_dec(v_unused_3736_);
v___x_3728_ = v_s_3720_;
v_isShared_3729_ = v_isSharedCheck_3735_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_recoveredErrors_3726_);
lean_inc(v_cache_3725_);
lean_inc(v_pos_3724_);
lean_inc(v_lhsPrec_3723_);
lean_inc(v_stxStack_3722_);
lean_dec(v_s_3720_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3735_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3730_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3722_, v_startStackSize_3721_);
v___x_3731_ = lean_box(0);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 4, v___x_3731_);
lean_ctor_set(v___x_3728_, 0, v___x_3730_);
v___x_3733_ = v___x_3728_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_lhsPrec_3723_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_pos_3724_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_cache_3725_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3734_, 5, v_recoveredErrors_3726_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3737_, lean_object* v_startStackSize_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_Parser_ParserState_keepLatest(v_s_3737_, v_startStackSize_3738_);
lean_dec(v_startStackSize_3738_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3740_, lean_object* v_startStackSize_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Parser_ParserState_keepLatest(v_s_3740_, v_startStackSize_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3743_, lean_object* v_startStackSize_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3743_, v_startStackSize_3744_);
lean_dec(v_startStackSize_3744_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3747_){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3749_ = l_Lean_Parser_ParserState_mkError(v_s_3747_, v___x_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3750_, lean_object* v_startLhsPrec_3751_, lean_object* v_p_3752_, lean_object* v_c_3753_, lean_object* v_s_3754_){
_start:
{
lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3762_; lean_object* v_s_3763_; lean_object* v_stxStack_3773_; lean_object* v_pos_3774_; lean_object* v_cache_3775_; lean_object* v_errorMsg_3776_; lean_object* v_recoveredErrors_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3790_; 
v_stxStack_3773_ = lean_ctor_get(v_s_3754_, 0);
v_pos_3774_ = lean_ctor_get(v_s_3754_, 2);
v_cache_3775_ = lean_ctor_get(v_s_3754_, 3);
v_errorMsg_3776_ = lean_ctor_get(v_s_3754_, 4);
v_recoveredErrors_3777_ = lean_ctor_get(v_s_3754_, 5);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_s_3754_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v_s_3754_, 1);
lean_dec(v_unused_3791_);
v___x_3779_ = v_s_3754_;
v_isShared_3780_ = v_isSharedCheck_3790_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_recoveredErrors_3777_);
lean_inc(v_errorMsg_3776_);
lean_inc(v_cache_3775_);
lean_inc(v_pos_3774_);
lean_inc(v_stxStack_3773_);
lean_dec(v_s_3754_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3790_;
goto v_resetjp_3778_;
}
v___jp_3755_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = l_Lean_Parser_ParserState_shrinkStack(v___y_3757_, v___y_3756_);
lean_dec(v___y_3756_);
v___x_3759_ = lean_box(0);
v___x_3760_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3758_, v___x_3759_);
return v___x_3760_;
}
v___jp_3761_:
{
lean_object* v_s_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; 
v_s_3764_ = lean_apply_2(v_p_3752_, v_c_3753_, v_s_3763_);
v___x_3765_ = l_Lean_Parser_ParserState_stackSize(v_s_3764_);
v___x_3766_ = lean_unsigned_to_nat(1u);
v___x_3767_ = lean_nat_add(v___y_3762_, v___x_3766_);
v___x_3768_ = lean_nat_dec_eq(v___x_3765_, v___x_3767_);
lean_dec(v___x_3767_);
lean_dec(v___x_3765_);
if (v___x_3768_ == 0)
{
lean_object* v_errorMsg_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_errorMsg_3769_ = lean_ctor_get(v_s_3764_, 4);
lean_inc(v_errorMsg_3769_);
v___x_3770_ = lean_box(0);
v___x_3771_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
v___y_3756_ = v___y_3762_;
v___y_3757_ = v_s_3764_;
goto v___jp_3755_;
}
else
{
if (v___x_3768_ == 0)
{
lean_object* v___x_3772_; 
lean_dec(v___y_3762_);
v___x_3772_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3764_);
return v___x_3772_;
}
else
{
v___y_3756_ = v___y_3762_;
v___y_3757_ = v_s_3764_;
goto v___jp_3755_;
}
}
}
else
{
lean_dec(v___y_3762_);
return v_s_3764_;
}
}
v_resetjp_3778_:
{
lean_object* v___y_3782_; 
if (lean_obj_tag(v_left_x3f_3750_) == 0)
{
lean_object* v___x_3789_; 
lean_dec(v_startLhsPrec_3751_);
v___x_3789_ = l_Lean_Parser_maxPrec;
v___y_3782_ = v___x_3789_;
goto v___jp_3781_;
}
else
{
v___y_3782_ = v_startLhsPrec_3751_;
goto v___jp_3781_;
}
v___jp_3781_:
{
lean_object* v_s_3784_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v___y_3782_);
v_s_3784_ = v___x_3779_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_stxStack_3773_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___y_3782_);
lean_ctor_set(v_reuseFailAlloc_3788_, 2, v_pos_3774_);
lean_ctor_set(v_reuseFailAlloc_3788_, 3, v_cache_3775_);
lean_ctor_set(v_reuseFailAlloc_3788_, 4, v_errorMsg_3776_);
lean_ctor_set(v_reuseFailAlloc_3788_, 5, v_recoveredErrors_3777_);
v_s_3784_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v_startSize_3785_; 
v_startSize_3785_ = l_Lean_Parser_ParserState_stackSize(v_s_3784_);
if (lean_obj_tag(v_left_x3f_3750_) == 1)
{
lean_object* v_val_3786_; lean_object* v_s_3787_; 
v_val_3786_ = lean_ctor_get(v_left_x3f_3750_, 0);
lean_inc(v_val_3786_);
lean_dec_ref(v_left_x3f_3750_);
v_s_3787_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3784_, v_val_3786_);
v___y_3762_ = v_startSize_3785_;
v_s_3763_ = v_s_3787_;
goto v___jp_3761_;
}
else
{
lean_dec(v_left_x3f_3750_);
v___y_3762_ = v_startSize_3785_;
v_s_3763_ = v_s_3784_;
goto v___jp_3761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3792_, lean_object* v_prio_3793_){
_start:
{
lean_object* v_pos_3794_; lean_object* v_errorMsg_3795_; lean_object* v___y_3797_; 
v_pos_3794_ = lean_ctor_get(v_s_3792_, 2);
v_errorMsg_3795_ = lean_ctor_get(v_s_3792_, 4);
if (lean_obj_tag(v_errorMsg_3795_) == 0)
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_unsigned_to_nat(1u);
v___y_3797_ = v___x_3800_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_unsigned_to_nat(0u);
v___y_3797_ = v___x_3801_;
goto v___jp_3796_;
}
v___jp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___y_3797_);
lean_ctor_set(v___x_3798_, 1, v_prio_3793_);
lean_inc(v_pos_3794_);
v___x_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3799_, 0, v_pos_3794_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3802_, lean_object* v_prio_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3802_, v_prio_3803_);
lean_dec_ref(v_s_3802_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3805_, lean_object* v_startSize_3806_, lean_object* v_startLhsPrec_3807_, lean_object* v_startPos_3808_, lean_object* v_prevPrio_3809_, lean_object* v_prio_3810_, lean_object* v_p_3811_, lean_object* v_c_3812_, lean_object* v_s_3813_){
_start:
{
lean_object* v_lhsPrec_3814_; lean_object* v_pos_3815_; lean_object* v_errorMsg_3816_; lean_object* v_previousScore_3817_; lean_object* v_fst_3818_; lean_object* v_snd_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3875_; 
v_lhsPrec_3814_ = lean_ctor_get(v_s_3813_, 1);
lean_inc(v_lhsPrec_3814_);
v_pos_3815_ = lean_ctor_get(v_s_3813_, 2);
lean_inc(v_pos_3815_);
v_errorMsg_3816_ = lean_ctor_get(v_s_3813_, 4);
lean_inc(v_errorMsg_3816_);
lean_inc(v_prevPrio_3809_);
v_previousScore_3817_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3813_, v_prevPrio_3809_);
v_fst_3818_ = lean_ctor_get(v_previousScore_3817_, 0);
v_snd_3819_ = lean_ctor_get(v_previousScore_3817_, 1);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_previousScore_3817_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3821_ = v_previousScore_3817_;
v_isShared_3822_ = v_isSharedCheck_3875_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_snd_3819_);
lean_inc(v_fst_3818_);
lean_dec(v_previousScore_3817_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3875_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v_prevSize_3823_; lean_object* v_s_3824_; lean_object* v_s_3825_; lean_object* v___x_3834_; lean_object* v_fst_3835_; lean_object* v_snd_3836_; uint8_t v___x_3837_; 
v_prevSize_3823_ = l_Lean_Parser_ParserState_stackSize(v_s_3813_);
v_s_3824_ = l_Lean_Parser_ParserState_restore(v_s_3813_, v_prevSize_3823_, v_startPos_3808_);
v_s_3825_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3805_, v_startLhsPrec_3807_, v_p_3811_, v_c_3812_, v_s_3824_);
lean_inc(v_prio_3810_);
v___x_3834_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3825_, v_prio_3810_);
v_fst_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_fst_3835_);
v_snd_3836_ = lean_ctor_get(v___x_3834_, 1);
lean_inc(v_snd_3836_);
lean_dec_ref(v___x_3834_);
v___x_3837_ = lean_nat_dec_lt(v_fst_3818_, v_fst_3835_);
if (v___x_3837_ == 0)
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_nat_dec_eq(v_fst_3818_, v_fst_3835_);
lean_dec(v_fst_3835_);
lean_dec(v_fst_3818_);
if (v___x_3838_ == 0)
{
lean_dec(v_snd_3836_);
lean_del_object(v___x_3821_);
lean_dec(v_snd_3819_);
lean_dec(v_prio_3810_);
goto v___jp_3831_;
}
else
{
lean_object* v_fst_3839_; lean_object* v_snd_3840_; lean_object* v_fst_3841_; lean_object* v_snd_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3874_; 
v_fst_3839_ = lean_ctor_get(v_snd_3819_, 0);
lean_inc(v_fst_3839_);
v_snd_3840_ = lean_ctor_get(v_snd_3819_, 1);
lean_inc(v_snd_3840_);
lean_dec(v_snd_3819_);
v_fst_3841_ = lean_ctor_get(v_snd_3836_, 0);
v_snd_3842_ = lean_ctor_get(v_snd_3836_, 1);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_snd_3836_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3844_ = v_snd_3836_;
v_isShared_3845_ = v_isSharedCheck_3874_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_snd_3842_);
lean_inc(v_fst_3841_);
lean_dec(v_snd_3836_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3874_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_nat_dec_lt(v_fst_3839_, v_fst_3841_);
if (v___x_3846_ == 0)
{
uint8_t v___x_3847_; 
v___x_3847_ = lean_nat_dec_eq(v_fst_3839_, v_fst_3841_);
lean_dec(v_fst_3841_);
lean_dec(v_fst_3839_);
if (v___x_3847_ == 0)
{
lean_del_object(v___x_3844_);
lean_dec(v_snd_3842_);
lean_dec(v_snd_3840_);
lean_del_object(v___x_3821_);
lean_dec(v_prio_3810_);
goto v___jp_3831_;
}
else
{
uint8_t v___x_3848_; 
v___x_3848_ = lean_nat_dec_lt(v_snd_3840_, v_snd_3842_);
if (v___x_3848_ == 0)
{
uint8_t v___x_3849_; 
lean_del_object(v___x_3821_);
v___x_3849_ = lean_nat_dec_eq(v_snd_3840_, v_snd_3842_);
lean_dec(v_snd_3842_);
lean_dec(v_snd_3840_);
if (v___x_3849_ == 0)
{
lean_del_object(v___x_3844_);
lean_dec(v_prio_3810_);
goto v___jp_3831_;
}
else
{
lean_dec(v_pos_3815_);
lean_dec(v_prevPrio_3809_);
if (lean_obj_tag(v_errorMsg_3816_) == 0)
{
lean_object* v_stxStack_3850_; lean_object* v_lhsPrec_3851_; lean_object* v_pos_3852_; lean_object* v_cache_3853_; lean_object* v_errorMsg_3854_; lean_object* v_recoveredErrors_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v_prevSize_3823_);
v_stxStack_3850_ = lean_ctor_get(v_s_3825_, 0);
v_lhsPrec_3851_ = lean_ctor_get(v_s_3825_, 1);
v_pos_3852_ = lean_ctor_get(v_s_3825_, 2);
v_cache_3853_ = lean_ctor_get(v_s_3825_, 3);
v_errorMsg_3854_ = lean_ctor_get(v_s_3825_, 4);
v_recoveredErrors_3855_ = lean_ctor_get(v_s_3825_, 5);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_s_3825_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3857_ = v_s_3825_;
v_isShared_3858_ = v_isSharedCheck_3868_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_recoveredErrors_3855_);
lean_inc(v_errorMsg_3854_);
lean_inc(v_cache_3853_);
lean_inc(v_pos_3852_);
lean_inc(v_lhsPrec_3851_);
lean_inc(v_stxStack_3850_);
lean_dec(v_s_3825_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3868_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___y_3860_; uint8_t v___x_3867_; 
v___x_3867_ = lean_nat_dec_le(v_lhsPrec_3851_, v_lhsPrec_3814_);
if (v___x_3867_ == 0)
{
lean_dec(v_lhsPrec_3851_);
v___y_3860_ = v_lhsPrec_3814_;
goto v___jp_3859_;
}
else
{
lean_dec(v_lhsPrec_3814_);
v___y_3860_ = v_lhsPrec_3851_;
goto v___jp_3859_;
}
v___jp_3859_:
{
lean_object* v___x_3862_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___y_3860_);
v___x_3862_ = v___x_3857_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_stxStack_3850_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___y_3860_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_pos_3852_);
lean_ctor_set(v_reuseFailAlloc_3866_, 3, v_cache_3853_);
lean_ctor_set(v_reuseFailAlloc_3866_, 4, v_errorMsg_3854_);
lean_ctor_set(v_reuseFailAlloc_3866_, 5, v_recoveredErrors_3855_);
v___x_3862_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3864_; 
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 1, v_prio_3810_);
lean_ctor_set(v___x_3844_, 0, v___x_3862_);
v___x_3864_ = v___x_3844_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_prio_3810_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
else
{
lean_object* v_val_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_dec(v_lhsPrec_3814_);
v_val_3869_ = lean_ctor_get(v_errorMsg_3816_, 0);
lean_inc(v_val_3869_);
lean_dec_ref(v_errorMsg_3816_);
v___x_3870_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3825_, v_prevSize_3823_, v_val_3869_);
lean_dec(v_prevSize_3823_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 1, v_prio_3810_);
lean_ctor_set(v___x_3844_, 0, v___x_3870_);
v___x_3872_ = v___x_3844_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_prio_3810_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_del_object(v___x_3844_);
lean_dec(v_snd_3842_);
lean_dec(v_snd_3840_);
lean_dec(v_prevSize_3823_);
lean_dec(v_errorMsg_3816_);
lean_dec(v_pos_3815_);
lean_dec(v_lhsPrec_3814_);
lean_dec(v_prevPrio_3809_);
goto v___jp_3826_;
}
}
}
else
{
lean_del_object(v___x_3844_);
lean_dec(v_snd_3842_);
lean_dec(v_fst_3841_);
lean_dec(v_snd_3840_);
lean_dec(v_fst_3839_);
lean_dec(v_prevSize_3823_);
lean_dec(v_errorMsg_3816_);
lean_dec(v_pos_3815_);
lean_dec(v_lhsPrec_3814_);
lean_dec(v_prevPrio_3809_);
goto v___jp_3826_;
}
}
}
}
else
{
lean_dec(v_snd_3836_);
lean_dec(v_fst_3835_);
lean_dec(v_prevSize_3823_);
lean_dec(v_snd_3819_);
lean_dec(v_fst_3818_);
lean_dec(v_errorMsg_3816_);
lean_dec(v_pos_3815_);
lean_dec(v_lhsPrec_3814_);
lean_dec(v_prevPrio_3809_);
goto v___jp_3826_;
}
v___jp_3826_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = l_Lean_Parser_ParserState_keepNewError(v_s_3825_, v_startSize_3806_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v_prio_3810_);
lean_ctor_set(v___x_3821_, 0, v___x_3827_);
v___x_3829_ = v___x_3821_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_prio_3810_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
v___jp_3831_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3825_, v_prevSize_3823_, v_pos_3815_, v_errorMsg_3816_, v_lhsPrec_3814_);
lean_dec(v_prevSize_3823_);
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v_prevPrio_3809_);
return v___x_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3876_, lean_object* v_startSize_3877_, lean_object* v_startLhsPrec_3878_, lean_object* v_startPos_3879_, lean_object* v_prevPrio_3880_, lean_object* v_prio_3881_, lean_object* v_p_3882_, lean_object* v_c_3883_, lean_object* v_s_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3876_, v_startSize_3877_, v_startLhsPrec_3878_, v_startPos_3879_, v_prevPrio_3880_, v_prio_3881_, v_p_3882_, v_c_3883_, v_s_3884_);
lean_dec(v_startSize_3877_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3886_, lean_object* v_s_3887_){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3888_ = lean_unsigned_to_nat(1u);
v___x_3889_ = lean_nat_add(v_startSize_3886_, v___x_3888_);
v___x_3890_ = l_Lean_Parser_ParserState_stackSize(v_s_3887_);
v___x_3891_ = lean_nat_dec_lt(v___x_3889_, v___x_3890_);
lean_dec(v___x_3890_);
lean_dec(v___x_3889_);
if (v___x_3891_ == 0)
{
return v_s_3887_;
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3893_ = l_Lean_Parser_ParserState_mkNode(v_s_3887_, v___x_3892_, v_startSize_3886_);
return v___x_3893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3894_, lean_object* v_s_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3894_, v_s_3895_);
lean_dec(v_startSize_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3897_, lean_object* v_startSize_3898_, lean_object* v_startLhsPrec_3899_, lean_object* v_startPos_3900_, lean_object* v_prevPrio_3901_, lean_object* v_ps_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
if (lean_obj_tag(v_ps_3902_) == 0)
{
lean_object* v___x_3905_; 
lean_dec_ref(v_a_3903_);
lean_dec(v_prevPrio_3901_);
lean_dec(v_startPos_3900_);
lean_dec(v_startLhsPrec_3899_);
lean_dec(v_left_x3f_3897_);
v___x_3905_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3898_, v_a_3904_);
return v___x_3905_;
}
else
{
lean_object* v_head_3906_; lean_object* v_fst_3907_; lean_object* v_tail_3908_; lean_object* v_snd_3909_; lean_object* v_fn_3910_; lean_object* v___x_3911_; lean_object* v_fst_3912_; lean_object* v_snd_3913_; 
v_head_3906_ = lean_ctor_get(v_ps_3902_, 0);
lean_inc(v_head_3906_);
v_fst_3907_ = lean_ctor_get(v_head_3906_, 0);
lean_inc(v_fst_3907_);
v_tail_3908_ = lean_ctor_get(v_ps_3902_, 1);
lean_inc(v_tail_3908_);
lean_dec_ref(v_ps_3902_);
v_snd_3909_ = lean_ctor_get(v_head_3906_, 1);
lean_inc(v_snd_3909_);
lean_dec(v_head_3906_);
v_fn_3910_ = lean_ctor_get(v_fst_3907_, 1);
lean_inc_ref(v_fn_3910_);
lean_dec(v_fst_3907_);
lean_inc_ref(v_a_3903_);
lean_inc(v_startPos_3900_);
lean_inc(v_startLhsPrec_3899_);
lean_inc(v_left_x3f_3897_);
v___x_3911_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3897_, v_startSize_3898_, v_startLhsPrec_3899_, v_startPos_3900_, v_prevPrio_3901_, v_snd_3909_, v_fn_3910_, v_a_3903_, v_a_3904_);
v_fst_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_fst_3912_);
v_snd_3913_ = lean_ctor_get(v___x_3911_, 1);
lean_inc(v_snd_3913_);
lean_dec_ref(v___x_3911_);
v_prevPrio_3901_ = v_snd_3913_;
v_ps_3902_ = v_tail_3908_;
v_a_3904_ = v_fst_3912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3915_, lean_object* v_startSize_3916_, lean_object* v_startLhsPrec_3917_, lean_object* v_startPos_3918_, lean_object* v_prevPrio_3919_, lean_object* v_ps_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3915_, v_startSize_3916_, v_startLhsPrec_3917_, v_startPos_3918_, v_prevPrio_3919_, v_ps_3920_, v_a_3921_, v_a_3922_);
lean_dec(v_startSize_3916_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3924_, lean_object* v_startSize_3925_, lean_object* v_startLhsPrec_3926_, lean_object* v_startPos_3927_, lean_object* v_prevPrio_3928_, lean_object* v_ps_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3924_, v_startSize_3925_, v_startLhsPrec_3926_, v_startPos_3927_, v_prevPrio_3928_, v_ps_3929_, v_a_3930_, v_a_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3933_, lean_object* v_startSize_3934_, lean_object* v_startLhsPrec_3935_, lean_object* v_startPos_3936_, lean_object* v_prevPrio_3937_, lean_object* v_ps_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3933_, v_startSize_3934_, v_startLhsPrec_3935_, v_startPos_3936_, v_prevPrio_3937_, v_ps_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_startSize_3934_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3943_, lean_object* v_x_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
if (lean_obj_tag(v_x_3944_) == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
lean_dec_ref(v_a_3945_);
lean_dec(v_left_x3f_3943_);
v___x_3947_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3948_ = l_Lean_Parser_ParserState_mkError(v_a_3946_, v___x_3947_);
return v___x_3948_;
}
else
{
lean_object* v_tail_3949_; 
v_tail_3949_ = lean_ctor_get(v_x_3944_, 1);
if (lean_obj_tag(v_tail_3949_) == 0)
{
lean_object* v_head_3950_; lean_object* v_fst_3951_; lean_object* v_lhsPrec_3952_; lean_object* v_fn_3953_; lean_object* v___x_3954_; 
v_head_3950_ = lean_ctor_get(v_x_3944_, 0);
lean_inc(v_head_3950_);
lean_dec_ref(v_x_3944_);
v_fst_3951_ = lean_ctor_get(v_head_3950_, 0);
lean_inc(v_fst_3951_);
lean_dec(v_head_3950_);
v_lhsPrec_3952_ = lean_ctor_get(v_a_3946_, 1);
lean_inc(v_lhsPrec_3952_);
v_fn_3953_ = lean_ctor_get(v_fst_3951_, 1);
lean_inc_ref(v_fn_3953_);
lean_dec(v_fst_3951_);
v___x_3954_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3943_, v_lhsPrec_3952_, v_fn_3953_, v_a_3945_, v_a_3946_);
return v___x_3954_;
}
else
{
lean_object* v_head_3955_; lean_object* v_fst_3956_; lean_object* v_lhsPrec_3957_; lean_object* v_pos_3958_; lean_object* v_snd_3959_; lean_object* v_fn_3960_; lean_object* v_startSize_3961_; lean_object* v_s_3962_; lean_object* v___x_3963_; 
lean_inc(v_tail_3949_);
v_head_3955_ = lean_ctor_get(v_x_3944_, 0);
lean_inc(v_head_3955_);
lean_dec_ref(v_x_3944_);
v_fst_3956_ = lean_ctor_get(v_head_3955_, 0);
lean_inc(v_fst_3956_);
v_lhsPrec_3957_ = lean_ctor_get(v_a_3946_, 1);
lean_inc(v_lhsPrec_3957_);
v_pos_3958_ = lean_ctor_get(v_a_3946_, 2);
lean_inc(v_pos_3958_);
v_snd_3959_ = lean_ctor_get(v_head_3955_, 1);
lean_inc(v_snd_3959_);
lean_dec(v_head_3955_);
v_fn_3960_ = lean_ctor_get(v_fst_3956_, 1);
lean_inc_ref(v_fn_3960_);
lean_dec(v_fst_3956_);
v_startSize_3961_ = l_Lean_Parser_ParserState_stackSize(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_lhsPrec_3957_);
lean_inc(v_left_x3f_3943_);
v_s_3962_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3943_, v_lhsPrec_3957_, v_fn_3960_, v_a_3945_, v_a_3946_);
v___x_3963_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3943_, v_startSize_3961_, v_lhsPrec_3957_, v_pos_3958_, v_snd_3959_, v_tail_3949_, v_a_3945_, v_s_3962_);
lean_dec(v_startSize_3961_);
return v___x_3963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_3965_, lean_object* v_x_3966_, lean_object* v_x_3967_){
_start:
{
if (lean_obj_tag(v_x_3965_) == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec_ref(v_x_3966_);
v___x_3968_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_3969_ = l_Lean_Parser_ParserState_mkError(v_x_3967_, v___x_3968_);
return v___x_3969_;
}
else
{
lean_object* v_tail_3970_; 
v_tail_3970_ = lean_ctor_get(v_x_3965_, 1);
if (lean_obj_tag(v_tail_3970_) == 0)
{
lean_object* v_head_3971_; lean_object* v_fn_3972_; lean_object* v___x_3973_; 
v_head_3971_ = lean_ctor_get(v_x_3965_, 0);
lean_inc(v_head_3971_);
lean_dec_ref(v_x_3965_);
v_fn_3972_ = lean_ctor_get(v_head_3971_, 1);
lean_inc_ref(v_fn_3972_);
lean_dec(v_head_3971_);
v___x_3973_ = lean_apply_2(v_fn_3972_, v_x_3966_, v_x_3967_);
return v___x_3973_;
}
else
{
lean_object* v_head_3974_; lean_object* v_fn_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_inc(v_tail_3970_);
v_head_3974_ = lean_ctor_get(v_x_3965_, 0);
lean_inc(v_head_3974_);
lean_dec_ref(v_x_3965_);
v_fn_3975_ = lean_ctor_get(v_head_3974_, 1);
lean_inc_ref(v_fn_3975_);
lean_dec(v_head_3974_);
v___x_3976_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_3976_, 0, v_tail_3970_);
v___x_3977_ = l_Lean_Parser_orelseFn(v_fn_3975_, v___x_3976_, v_x_3966_, v_x_3967_);
return v___x_3977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_3978_, lean_object* v_c_3979_, lean_object* v_s_3980_){
_start:
{
lean_object* v_toCacheableParserContext_3981_; lean_object* v_savedPos_x3f_3982_; 
v_toCacheableParserContext_3981_ = lean_ctor_get(v_c_3979_, 2);
v_savedPos_x3f_3982_ = lean_ctor_get(v_toCacheableParserContext_3981_, 2);
lean_inc(v_savedPos_x3f_3982_);
if (lean_obj_tag(v_savedPos_x3f_3982_) == 0)
{
lean_dec_ref(v_c_3979_);
lean_dec_ref(v_errorMsg_3978_);
return v_s_3980_;
}
else
{
lean_object* v_toInputContext_3983_; lean_object* v_val_3984_; lean_object* v_fileMap_3985_; lean_object* v_pos_3986_; lean_object* v_savedPos_3987_; lean_object* v_pos_3988_; lean_object* v_column_3989_; lean_object* v_column_3990_; uint8_t v___x_3991_; 
v_toInputContext_3983_ = lean_ctor_get(v_c_3979_, 0);
lean_inc_ref(v_toInputContext_3983_);
lean_dec_ref(v_c_3979_);
v_val_3984_ = lean_ctor_get(v_savedPos_x3f_3982_, 0);
lean_inc(v_val_3984_);
lean_dec_ref(v_savedPos_x3f_3982_);
v_fileMap_3985_ = lean_ctor_get(v_toInputContext_3983_, 2);
lean_inc_ref(v_fileMap_3985_);
lean_dec_ref(v_toInputContext_3983_);
v_pos_3986_ = lean_ctor_get(v_s_3980_, 2);
lean_inc_ref(v_fileMap_3985_);
v_savedPos_3987_ = l_Lean_FileMap_toPosition(v_fileMap_3985_, v_val_3984_);
lean_dec(v_val_3984_);
v_pos_3988_ = l_Lean_FileMap_toPosition(v_fileMap_3985_, v_pos_3986_);
v_column_3989_ = lean_ctor_get(v_pos_3988_, 1);
lean_inc(v_column_3989_);
lean_dec_ref(v_pos_3988_);
v_column_3990_ = lean_ctor_get(v_savedPos_3987_, 1);
lean_inc(v_column_3990_);
lean_dec_ref(v_savedPos_3987_);
v___x_3991_ = lean_nat_dec_eq(v_column_3989_, v_column_3990_);
lean_dec(v_column_3990_);
lean_dec(v_column_3989_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Lean_Parser_ParserState_mkError(v_s_3980_, v_errorMsg_3978_);
return v___x_3992_;
}
else
{
lean_dec_ref(v_errorMsg_3978_);
return v_s_3980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_3993_){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_3995_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_3995_, 0, v_errorMsg_3993_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = ((lean_object*)(l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4005_ = ((lean_object*)(l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4006_ = l_Lean_addBuiltinDocString(v___x_4004_, v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4009_, lean_object* v_c_4010_, lean_object* v_s_4011_){
_start:
{
lean_object* v_toCacheableParserContext_4012_; lean_object* v_savedPos_x3f_4013_; 
v_toCacheableParserContext_4012_ = lean_ctor_get(v_c_4010_, 2);
v_savedPos_x3f_4013_ = lean_ctor_get(v_toCacheableParserContext_4012_, 2);
lean_inc(v_savedPos_x3f_4013_);
if (lean_obj_tag(v_savedPos_x3f_4013_) == 0)
{
lean_dec_ref(v_c_4010_);
lean_dec_ref(v_errorMsg_4009_);
return v_s_4011_;
}
else
{
lean_object* v_toInputContext_4014_; lean_object* v_val_4015_; lean_object* v_fileMap_4016_; lean_object* v_pos_4017_; lean_object* v_savedPos_4018_; lean_object* v_column_4019_; lean_object* v_pos_4020_; lean_object* v_column_4021_; uint8_t v___x_4022_; 
v_toInputContext_4014_ = lean_ctor_get(v_c_4010_, 0);
lean_inc_ref(v_toInputContext_4014_);
lean_dec_ref(v_c_4010_);
v_val_4015_ = lean_ctor_get(v_savedPos_x3f_4013_, 0);
lean_inc(v_val_4015_);
lean_dec_ref(v_savedPos_x3f_4013_);
v_fileMap_4016_ = lean_ctor_get(v_toInputContext_4014_, 2);
lean_inc_ref(v_fileMap_4016_);
lean_dec_ref(v_toInputContext_4014_);
v_pos_4017_ = lean_ctor_get(v_s_4011_, 2);
lean_inc_ref(v_fileMap_4016_);
v_savedPos_4018_ = l_Lean_FileMap_toPosition(v_fileMap_4016_, v_val_4015_);
lean_dec(v_val_4015_);
v_column_4019_ = lean_ctor_get(v_savedPos_4018_, 1);
lean_inc(v_column_4019_);
lean_dec_ref(v_savedPos_4018_);
v_pos_4020_ = l_Lean_FileMap_toPosition(v_fileMap_4016_, v_pos_4017_);
v_column_4021_ = lean_ctor_get(v_pos_4020_, 1);
lean_inc(v_column_4021_);
lean_dec_ref(v_pos_4020_);
v___x_4022_ = lean_nat_dec_le(v_column_4019_, v_column_4021_);
lean_dec(v_column_4021_);
lean_dec(v_column_4019_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_Parser_ParserState_mkError(v_s_4011_, v_errorMsg_4009_);
return v___x_4023_;
}
else
{
lean_dec_ref(v_errorMsg_4009_);
return v_s_4011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4024_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4025_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4026_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4026_, 0, v_errorMsg_4024_);
v___x_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4025_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = ((lean_object*)(l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4036_ = ((lean_object*)(l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4037_ = l_Lean_addBuiltinDocString(v___x_4035_, v___x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4040_, lean_object* v_c_4041_, lean_object* v_s_4042_){
_start:
{
lean_object* v_toCacheableParserContext_4043_; lean_object* v_savedPos_x3f_4044_; 
v_toCacheableParserContext_4043_ = lean_ctor_get(v_c_4041_, 2);
v_savedPos_x3f_4044_ = lean_ctor_get(v_toCacheableParserContext_4043_, 2);
lean_inc(v_savedPos_x3f_4044_);
if (lean_obj_tag(v_savedPos_x3f_4044_) == 0)
{
lean_dec_ref(v_c_4041_);
lean_dec_ref(v_errorMsg_4040_);
return v_s_4042_;
}
else
{
lean_object* v_toInputContext_4045_; lean_object* v_val_4046_; lean_object* v_fileMap_4047_; lean_object* v_pos_4048_; lean_object* v_savedPos_4049_; lean_object* v_column_4050_; lean_object* v_pos_4051_; lean_object* v_column_4052_; uint8_t v___x_4053_; 
v_toInputContext_4045_ = lean_ctor_get(v_c_4041_, 0);
lean_inc_ref(v_toInputContext_4045_);
lean_dec_ref(v_c_4041_);
v_val_4046_ = lean_ctor_get(v_savedPos_x3f_4044_, 0);
lean_inc(v_val_4046_);
lean_dec_ref(v_savedPos_x3f_4044_);
v_fileMap_4047_ = lean_ctor_get(v_toInputContext_4045_, 2);
lean_inc_ref(v_fileMap_4047_);
lean_dec_ref(v_toInputContext_4045_);
v_pos_4048_ = lean_ctor_get(v_s_4042_, 2);
lean_inc_ref(v_fileMap_4047_);
v_savedPos_4049_ = l_Lean_FileMap_toPosition(v_fileMap_4047_, v_val_4046_);
lean_dec(v_val_4046_);
v_column_4050_ = lean_ctor_get(v_savedPos_4049_, 1);
lean_inc(v_column_4050_);
lean_dec_ref(v_savedPos_4049_);
v_pos_4051_ = l_Lean_FileMap_toPosition(v_fileMap_4047_, v_pos_4048_);
v_column_4052_ = lean_ctor_get(v_pos_4051_, 1);
lean_inc(v_column_4052_);
lean_dec_ref(v_pos_4051_);
v___x_4053_ = lean_nat_dec_lt(v_column_4050_, v_column_4052_);
lean_dec(v_column_4052_);
lean_dec(v_column_4050_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Parser_ParserState_mkError(v_s_4042_, v_errorMsg_4040_);
return v___x_4054_;
}
else
{
lean_dec_ref(v_errorMsg_4040_);
return v_s_4042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4055_){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4057_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4057_, 0, v_errorMsg_4055_);
v___x_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4056_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = ((lean_object*)(l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4067_ = ((lean_object*)(l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4068_ = l_Lean_addBuiltinDocString(v___x_4066_, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4071_, lean_object* v_c_4072_, lean_object* v_s_4073_){
_start:
{
lean_object* v_toCacheableParserContext_4074_; lean_object* v_savedPos_x3f_4075_; 
v_toCacheableParserContext_4074_ = lean_ctor_get(v_c_4072_, 2);
v_savedPos_x3f_4075_ = lean_ctor_get(v_toCacheableParserContext_4074_, 2);
lean_inc(v_savedPos_x3f_4075_);
if (lean_obj_tag(v_savedPos_x3f_4075_) == 0)
{
lean_dec_ref(v_c_4072_);
lean_dec_ref(v_errorMsg_4071_);
return v_s_4073_;
}
else
{
lean_object* v_toInputContext_4076_; lean_object* v_val_4077_; lean_object* v_fileMap_4078_; lean_object* v_pos_4079_; lean_object* v_savedPos_4080_; lean_object* v_pos_4081_; lean_object* v_line_4082_; lean_object* v_line_4083_; uint8_t v___x_4084_; 
v_toInputContext_4076_ = lean_ctor_get(v_c_4072_, 0);
lean_inc_ref(v_toInputContext_4076_);
lean_dec_ref(v_c_4072_);
v_val_4077_ = lean_ctor_get(v_savedPos_x3f_4075_, 0);
lean_inc(v_val_4077_);
lean_dec_ref(v_savedPos_x3f_4075_);
v_fileMap_4078_ = lean_ctor_get(v_toInputContext_4076_, 2);
lean_inc_ref(v_fileMap_4078_);
lean_dec_ref(v_toInputContext_4076_);
v_pos_4079_ = lean_ctor_get(v_s_4073_, 2);
lean_inc_ref(v_fileMap_4078_);
v_savedPos_4080_ = l_Lean_FileMap_toPosition(v_fileMap_4078_, v_val_4077_);
lean_dec(v_val_4077_);
v_pos_4081_ = l_Lean_FileMap_toPosition(v_fileMap_4078_, v_pos_4079_);
v_line_4082_ = lean_ctor_get(v_pos_4081_, 0);
lean_inc(v_line_4082_);
lean_dec_ref(v_pos_4081_);
v_line_4083_ = lean_ctor_get(v_savedPos_4080_, 0);
lean_inc(v_line_4083_);
lean_dec_ref(v_savedPos_4080_);
v___x_4084_ = lean_nat_dec_eq(v_line_4082_, v_line_4083_);
lean_dec(v_line_4083_);
lean_dec(v_line_4082_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Parser_ParserState_mkError(v_s_4073_, v_errorMsg_4071_);
return v___x_4085_;
}
else
{
lean_dec_ref(v_errorMsg_4071_);
return v_s_4073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4086_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4088_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4088_, 0, v_errorMsg_4086_);
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = ((lean_object*)(l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4098_ = ((lean_object*)(l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4099_ = l_Lean_addBuiltinDocString(v___x_4097_, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4102_, lean_object* v_x_4103_){
_start:
{
lean_object* v_prec_4104_; lean_object* v_quotDepth_4105_; uint8_t v_suppressInsideQuot_4106_; lean_object* v_forbiddenTk_x3f_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4116_; 
v_prec_4104_ = lean_ctor_get(v_x_4103_, 0);
v_quotDepth_4105_ = lean_ctor_get(v_x_4103_, 1);
v_suppressInsideQuot_4106_ = lean_ctor_get_uint8(v_x_4103_, sizeof(void*)*4);
v_forbiddenTk_x3f_4107_ = lean_ctor_get(v_x_4103_, 3);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_x_4103_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v_x_4103_, 2);
lean_dec(v_unused_4117_);
v___x_4109_ = v_x_4103_;
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4107_);
lean_inc(v_quotDepth_4105_);
lean_inc(v_prec_4104_);
lean_dec(v_x_4103_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v_pos_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v_pos_4111_ = lean_ctor_get(v___y_4102_, 2);
lean_inc(v_pos_4111_);
v___x_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_pos_4111_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 2, v___x_4112_);
v___x_4114_ = v___x_4109_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_prec_4104_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_quotDepth_4105_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4115_, 3, v_forbiddenTk_x3f_4107_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, sizeof(void*)*4, v_suppressInsideQuot_4106_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4118_, lean_object* v_x_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_Parser_withPosition___lam__0(v___y_4118_, v_x_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___f_4124_; lean_object* v___x_4125_; 
lean_inc_ref(v___y_4123_);
v___f_4124_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4124_, 0, v___y_4123_);
v___x_4125_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4124_, v_fn_4121_, v___y_4122_, v___y_4123_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4126_){
_start:
{
lean_object* v_info_4127_; lean_object* v_fn_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4136_; 
v_info_4127_ = lean_ctor_get(v_p_4126_, 0);
v_fn_4128_ = lean_ctor_get(v_p_4126_, 1);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_p_4126_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4130_ = v_p_4126_;
v_isShared_4131_ = v_isSharedCheck_4136_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_fn_4128_);
lean_inc(v_info_4127_);
lean_dec(v_p_4126_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4136_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___f_4132_; lean_object* v___x_4134_; 
v___f_4132_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4132_, 0, v_fn_4128_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v___f_4132_);
v___x_4134_ = v___x_4130_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_info_4127_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___f_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = ((lean_object*)(l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4145_ = ((lean_object*)(l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4146_ = l_Lean_addBuiltinDocString(v___x_4144_, v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4149_, lean_object* v_pos_4150_, lean_object* v_c_4151_){
_start:
{
uint8_t v___x_4152_; 
v___x_4152_ = l_Lean_Parser_checkTailLinebreak(v_prev_4149_);
if (v___x_4152_ == 0)
{
lean_dec(v_pos_4150_);
return v_c_4151_;
}
else
{
lean_object* v_prec_4153_; lean_object* v_quotDepth_4154_; uint8_t v_suppressInsideQuot_4155_; lean_object* v_forbiddenTk_x3f_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4164_; 
v_prec_4153_ = lean_ctor_get(v_c_4151_, 0);
v_quotDepth_4154_ = lean_ctor_get(v_c_4151_, 1);
v_suppressInsideQuot_4155_ = lean_ctor_get_uint8(v_c_4151_, sizeof(void*)*4);
v_forbiddenTk_x3f_4156_ = lean_ctor_get(v_c_4151_, 3);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_c_4151_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; 
v_unused_4165_ = lean_ctor_get(v_c_4151_, 2);
lean_dec(v_unused_4165_);
v___x_4158_ = v_c_4151_;
v_isShared_4159_ = v_isSharedCheck_4164_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4156_);
lean_inc(v_quotDepth_4154_);
lean_inc(v_prec_4153_);
lean_dec(v_c_4151_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4164_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_pos_4150_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 2, v___x_4160_);
v___x_4162_ = v___x_4158_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_prec_4153_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_quotDepth_4154_);
lean_ctor_set(v_reuseFailAlloc_4163_, 2, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4163_, 3, v_forbiddenTk_x3f_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4163_, sizeof(void*)*4, v_suppressInsideQuot_4155_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4166_, lean_object* v_pos_4167_, lean_object* v_c_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4166_, v_pos_4167_, v_c_4168_);
lean_dec(v_prev_4166_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_stxStack_4173_; lean_object* v_pos_4174_; lean_object* v_prev_4175_; lean_object* v___f_4176_; lean_object* v___x_4177_; 
v_stxStack_4173_ = lean_ctor_get(v___y_4172_, 0);
v_pos_4174_ = lean_ctor_get(v___y_4172_, 2);
v_prev_4175_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4173_);
lean_inc(v_pos_4174_);
v___f_4176_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4176_, 0, v_prev_4175_);
lean_closure_set(v___f_4176_, 1, v_pos_4174_);
v___x_4177_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4176_, v_fn_4170_, v___y_4171_, v___y_4172_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4178_){
_start:
{
lean_object* v_info_4179_; lean_object* v_fn_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4188_; 
v_info_4179_ = lean_ctor_get(v_p_4178_, 0);
v_fn_4180_ = lean_ctor_get(v_p_4178_, 1);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_p_4178_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4182_ = v_p_4178_;
v_isShared_4183_ = v_isSharedCheck_4188_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_fn_4180_);
lean_inc(v_info_4179_);
lean_dec(v_p_4178_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4188_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___f_4184_; lean_object* v___x_4186_; 
v___f_4184_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4184_, 0, v_fn_4180_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 1, v___f_4184_);
v___x_4186_ = v___x_4182_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_info_4179_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___f_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4189_){
_start:
{
lean_object* v_prec_4190_; lean_object* v_quotDepth_4191_; uint8_t v_suppressInsideQuot_4192_; lean_object* v_forbiddenTk_x3f_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4201_; 
v_prec_4190_ = lean_ctor_get(v_x_4189_, 0);
v_quotDepth_4191_ = lean_ctor_get(v_x_4189_, 1);
v_suppressInsideQuot_4192_ = lean_ctor_get_uint8(v_x_4189_, sizeof(void*)*4);
v_forbiddenTk_x3f_4193_ = lean_ctor_get(v_x_4189_, 3);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; 
v_unused_4202_ = lean_ctor_get(v_x_4189_, 2);
lean_dec(v_unused_4202_);
v___x_4195_ = v_x_4189_;
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4193_);
lean_inc(v_quotDepth_4191_);
lean_inc(v_prec_4190_);
lean_dec(v_x_4189_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4197_ = lean_box(0);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 2, v___x_4197_);
v___x_4199_ = v___x_4195_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_prec_4190_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_quotDepth_4191_);
lean_ctor_set(v_reuseFailAlloc_4200_, 2, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_forbiddenTk_x3f_4193_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*4, v_suppressInsideQuot_4192_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4204_){
_start:
{
lean_object* v___f_4205_; lean_object* v___x_4206_; 
v___f_4205_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4206_ = l_Lean_Parser_adaptCacheableContext(v___f_4205_, v_p_4204_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = ((lean_object*)(l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4215_ = ((lean_object*)(l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4216_ = l_Lean_addBuiltinDocString(v___x_4214_, v___x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4219_, lean_object* v_x_4220_){
_start:
{
lean_object* v_prec_4221_; lean_object* v_quotDepth_4222_; uint8_t v_suppressInsideQuot_4223_; lean_object* v_savedPos_x3f_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4232_; 
v_prec_4221_ = lean_ctor_get(v_x_4220_, 0);
v_quotDepth_4222_ = lean_ctor_get(v_x_4220_, 1);
v_suppressInsideQuot_4223_ = lean_ctor_get_uint8(v_x_4220_, sizeof(void*)*4);
v_savedPos_x3f_4224_ = lean_ctor_get(v_x_4220_, 2);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_x_4220_);
if (v_isSharedCheck_4232_ == 0)
{
lean_object* v_unused_4233_; 
v_unused_4233_ = lean_ctor_get(v_x_4220_, 3);
lean_dec(v_unused_4233_);
v___x_4226_ = v_x_4220_;
v_isShared_4227_ = v_isSharedCheck_4232_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_savedPos_x3f_4224_);
lean_inc(v_quotDepth_4222_);
lean_inc(v_prec_4221_);
lean_dec(v_x_4220_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4232_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_tk_4219_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 3, v___x_4228_);
v___x_4230_ = v___x_4226_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_prec_4221_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_quotDepth_4222_);
lean_ctor_set(v_reuseFailAlloc_4231_, 2, v_savedPos_x3f_4224_);
lean_ctor_set(v_reuseFailAlloc_4231_, 3, v___x_4228_);
lean_ctor_set_uint8(v_reuseFailAlloc_4231_, sizeof(void*)*4, v_suppressInsideQuot_4223_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4234_, lean_object* v_p_4235_){
_start:
{
lean_object* v___f_4236_; lean_object* v___x_4237_; 
v___f_4236_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4236_, 0, v_tk_4234_);
v___x_4237_ = l_Lean_Parser_adaptCacheableContext(v___f_4236_, v_p_4235_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4245_ = ((lean_object*)(l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4246_ = ((lean_object*)(l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4247_ = l_Lean_addBuiltinDocString(v___x_4245_, v___x_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4250_){
_start:
{
lean_object* v_prec_4251_; lean_object* v_quotDepth_4252_; uint8_t v_suppressInsideQuot_4253_; lean_object* v_savedPos_x3f_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4262_; 
v_prec_4251_ = lean_ctor_get(v_x_4250_, 0);
v_quotDepth_4252_ = lean_ctor_get(v_x_4250_, 1);
v_suppressInsideQuot_4253_ = lean_ctor_get_uint8(v_x_4250_, sizeof(void*)*4);
v_savedPos_x3f_4254_ = lean_ctor_get(v_x_4250_, 2);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_x_4250_);
if (v_isSharedCheck_4262_ == 0)
{
lean_object* v_unused_4263_; 
v_unused_4263_ = lean_ctor_get(v_x_4250_, 3);
lean_dec(v_unused_4263_);
v___x_4256_ = v_x_4250_;
v_isShared_4257_ = v_isSharedCheck_4262_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_savedPos_x3f_4254_);
lean_inc(v_quotDepth_4252_);
lean_inc(v_prec_4251_);
lean_dec(v_x_4250_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4262_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4260_; 
v___x_4258_ = lean_box(0);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 3, v___x_4258_);
v___x_4260_ = v___x_4256_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_prec_4251_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_quotDepth_4252_);
lean_ctor_set(v_reuseFailAlloc_4261_, 2, v_savedPos_x3f_4254_);
lean_ctor_set(v_reuseFailAlloc_4261_, 3, v___x_4258_);
lean_ctor_set_uint8(v_reuseFailAlloc_4261_, sizeof(void*)*4, v_suppressInsideQuot_4253_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4265_){
_start:
{
lean_object* v___f_4266_; lean_object* v___x_4267_; 
v___f_4266_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4267_ = l_Lean_Parser_adaptCacheableContext(v___f_4266_, v_p_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4276_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4277_ = l_Lean_addBuiltinDocString(v___x_4275_, v___x_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4281_, lean_object* v_s_4282_){
_start:
{
lean_object* v_pos_4283_; lean_object* v_toInputContext_4284_; uint8_t v___x_4285_; 
v_pos_4283_ = lean_ctor_get(v_s_4282_, 2);
v_toInputContext_4284_ = lean_ctor_get(v_c_4281_, 0);
v___x_4285_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4284_, v_pos_4283_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4287_ = l_Lean_Parser_ParserState_mkError(v_s_4282_, v___x_4286_);
return v___x_4287_;
}
else
{
return v_s_4282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4288_, lean_object* v_s_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Parser_eoiFn(v_c_4288_, v_s_4289_);
lean_dec_ref(v_c_4288_);
return v_res_4290_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4292_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
lean_ctor_set(v___x_4293_, 1, v___x_4291_);
return v___x_4293_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4295_, lean_object* v_v_4296_, lean_object* v_t_4297_){
_start:
{
if (lean_obj_tag(v_t_4297_) == 0)
{
lean_object* v_size_4298_; lean_object* v_k_4299_; lean_object* v_v_4300_; lean_object* v_l_4301_; lean_object* v_r_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4582_; 
v_size_4298_ = lean_ctor_get(v_t_4297_, 0);
v_k_4299_ = lean_ctor_get(v_t_4297_, 1);
v_v_4300_ = lean_ctor_get(v_t_4297_, 2);
v_l_4301_ = lean_ctor_get(v_t_4297_, 3);
v_r_4302_ = lean_ctor_get(v_t_4297_, 4);
v_isSharedCheck_4582_ = !lean_is_exclusive(v_t_4297_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4304_ = v_t_4297_;
v_isShared_4305_ = v_isSharedCheck_4582_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_r_4302_);
lean_inc(v_l_4301_);
lean_inc(v_v_4300_);
lean_inc(v_k_4299_);
lean_inc(v_size_4298_);
lean_dec(v_t_4297_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4582_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
uint8_t v___x_4306_; 
v___x_4306_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4295_, v_k_4299_);
switch(v___x_4306_)
{
case 0:
{
lean_object* v_impl_4307_; lean_object* v___x_4308_; 
lean_dec(v_size_4298_);
v_impl_4307_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4295_, v_v_4296_, v_l_4301_);
v___x_4308_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4302_) == 0)
{
lean_object* v_size_4309_; lean_object* v_size_4310_; lean_object* v_k_4311_; lean_object* v_v_4312_; lean_object* v_l_4313_; lean_object* v_r_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v_size_4309_ = lean_ctor_get(v_r_4302_, 0);
v_size_4310_ = lean_ctor_get(v_impl_4307_, 0);
lean_inc(v_size_4310_);
v_k_4311_ = lean_ctor_get(v_impl_4307_, 1);
lean_inc(v_k_4311_);
v_v_4312_ = lean_ctor_get(v_impl_4307_, 2);
lean_inc(v_v_4312_);
v_l_4313_ = lean_ctor_get(v_impl_4307_, 3);
lean_inc(v_l_4313_);
v_r_4314_ = lean_ctor_get(v_impl_4307_, 4);
lean_inc(v_r_4314_);
v___x_4315_ = lean_unsigned_to_nat(3u);
v___x_4316_ = lean_nat_mul(v___x_4315_, v_size_4309_);
v___x_4317_ = lean_nat_dec_lt(v___x_4316_, v_size_4310_);
lean_dec(v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4321_; 
lean_dec(v_r_4314_);
lean_dec(v_l_4313_);
lean_dec(v_v_4312_);
lean_dec(v_k_4311_);
v___x_4318_ = lean_nat_add(v___x_4308_, v_size_4310_);
lean_dec(v_size_4310_);
v___x_4319_ = lean_nat_add(v___x_4318_, v_size_4309_);
lean_dec(v___x_4318_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 3, v_impl_4307_);
lean_ctor_set(v___x_4304_, 0, v___x_4319_);
v___x_4321_ = v___x_4304_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4319_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4322_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4322_, 3, v_impl_4307_);
lean_ctor_set(v_reuseFailAlloc_4322_, 4, v_r_4302_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
else
{
lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4388_; 
v_isSharedCheck_4388_ = !lean_is_exclusive(v_impl_4307_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; lean_object* v_unused_4390_; lean_object* v_unused_4391_; lean_object* v_unused_4392_; lean_object* v_unused_4393_; 
v_unused_4389_ = lean_ctor_get(v_impl_4307_, 4);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_impl_4307_, 3);
lean_dec(v_unused_4390_);
v_unused_4391_ = lean_ctor_get(v_impl_4307_, 2);
lean_dec(v_unused_4391_);
v_unused_4392_ = lean_ctor_get(v_impl_4307_, 1);
lean_dec(v_unused_4392_);
v_unused_4393_ = lean_ctor_get(v_impl_4307_, 0);
lean_dec(v_unused_4393_);
v___x_4324_ = v_impl_4307_;
v_isShared_4325_ = v_isSharedCheck_4388_;
goto v_resetjp_4323_;
}
else
{
lean_dec(v_impl_4307_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4388_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v_size_4326_; lean_object* v_size_4327_; lean_object* v_k_4328_; lean_object* v_v_4329_; lean_object* v_l_4330_; lean_object* v_r_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; 
v_size_4326_ = lean_ctor_get(v_l_4313_, 0);
v_size_4327_ = lean_ctor_get(v_r_4314_, 0);
v_k_4328_ = lean_ctor_get(v_r_4314_, 1);
v_v_4329_ = lean_ctor_get(v_r_4314_, 2);
v_l_4330_ = lean_ctor_get(v_r_4314_, 3);
v_r_4331_ = lean_ctor_get(v_r_4314_, 4);
v___x_4332_ = lean_unsigned_to_nat(2u);
v___x_4333_ = lean_nat_mul(v___x_4332_, v_size_4326_);
v___x_4334_ = lean_nat_dec_lt(v_size_4327_, v___x_4333_);
lean_dec(v___x_4333_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4363_; 
lean_inc(v_r_4331_);
lean_inc(v_l_4330_);
lean_inc(v_v_4329_);
lean_inc(v_k_4328_);
v_isSharedCheck_4363_ = !lean_is_exclusive(v_r_4314_);
if (v_isSharedCheck_4363_ == 0)
{
lean_object* v_unused_4364_; lean_object* v_unused_4365_; lean_object* v_unused_4366_; lean_object* v_unused_4367_; lean_object* v_unused_4368_; 
v_unused_4364_ = lean_ctor_get(v_r_4314_, 4);
lean_dec(v_unused_4364_);
v_unused_4365_ = lean_ctor_get(v_r_4314_, 3);
lean_dec(v_unused_4365_);
v_unused_4366_ = lean_ctor_get(v_r_4314_, 2);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v_r_4314_, 1);
lean_dec(v_unused_4367_);
v_unused_4368_ = lean_ctor_get(v_r_4314_, 0);
lean_dec(v_unused_4368_);
v___x_4336_ = v_r_4314_;
v_isShared_4337_ = v_isSharedCheck_4363_;
goto v_resetjp_4335_;
}
else
{
lean_dec(v_r_4314_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4363_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___x_4351_; lean_object* v___y_4353_; 
v___x_4338_ = lean_nat_add(v___x_4308_, v_size_4310_);
lean_dec(v_size_4310_);
v___x_4339_ = lean_nat_add(v___x_4338_, v_size_4309_);
lean_dec(v___x_4338_);
v___x_4351_ = lean_nat_add(v___x_4308_, v_size_4326_);
if (lean_obj_tag(v_l_4330_) == 0)
{
lean_object* v_size_4361_; 
v_size_4361_ = lean_ctor_get(v_l_4330_, 0);
lean_inc(v_size_4361_);
v___y_4353_ = v_size_4361_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4362_; 
v___x_4362_ = lean_unsigned_to_nat(0u);
v___y_4353_ = v___x_4362_;
goto v___jp_4352_;
}
v___jp_4340_:
{
lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4344_ = lean_nat_add(v___y_4341_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec(v___y_4341_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 4, v_r_4302_);
lean_ctor_set(v___x_4336_, 3, v_r_4331_);
lean_ctor_set(v___x_4336_, 2, v_v_4300_);
lean_ctor_set(v___x_4336_, 1, v_k_4299_);
lean_ctor_set(v___x_4336_, 0, v___x_4344_);
v___x_4346_ = v___x_4336_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4350_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4350_, 3, v_r_4331_);
lean_ctor_set(v_reuseFailAlloc_4350_, 4, v_r_4302_);
v___x_4346_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4348_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 4, v___x_4346_);
lean_ctor_set(v___x_4324_, 3, v___y_4342_);
lean_ctor_set(v___x_4324_, 2, v_v_4329_);
lean_ctor_set(v___x_4324_, 1, v_k_4328_);
lean_ctor_set(v___x_4324_, 0, v___x_4339_);
v___x_4348_ = v___x_4324_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v_k_4328_);
lean_ctor_set(v_reuseFailAlloc_4349_, 2, v_v_4329_);
lean_ctor_set(v_reuseFailAlloc_4349_, 3, v___y_4342_);
lean_ctor_set(v_reuseFailAlloc_4349_, 4, v___x_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
v___jp_4352_:
{
lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4354_ = lean_nat_add(v___x_4351_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec(v___x_4351_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_l_4330_);
lean_ctor_set(v___x_4304_, 3, v_l_4313_);
lean_ctor_set(v___x_4304_, 2, v_v_4312_);
lean_ctor_set(v___x_4304_, 1, v_k_4311_);
lean_ctor_set(v___x_4304_, 0, v___x_4354_);
v___x_4356_ = v___x_4304_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4354_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_k_4311_);
lean_ctor_set(v_reuseFailAlloc_4360_, 2, v_v_4312_);
lean_ctor_set(v_reuseFailAlloc_4360_, 3, v_l_4313_);
lean_ctor_set(v_reuseFailAlloc_4360_, 4, v_l_4330_);
v___x_4356_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_nat_add(v___x_4308_, v_size_4309_);
if (lean_obj_tag(v_r_4331_) == 0)
{
lean_object* v_size_4358_; 
v_size_4358_ = lean_ctor_get(v_r_4331_, 0);
lean_inc(v_size_4358_);
v___y_4341_ = v___x_4357_;
v___y_4342_ = v___x_4356_;
v___y_4343_ = v_size_4358_;
goto v___jp_4340_;
}
else
{
lean_object* v___x_4359_; 
v___x_4359_ = lean_unsigned_to_nat(0u);
v___y_4341_ = v___x_4357_;
v___y_4342_ = v___x_4356_;
v___y_4343_ = v___x_4359_;
goto v___jp_4340_;
}
}
}
}
}
else
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
lean_del_object(v___x_4304_);
v___x_4369_ = lean_nat_add(v___x_4308_, v_size_4310_);
lean_dec(v_size_4310_);
v___x_4370_ = lean_nat_add(v___x_4369_, v_size_4309_);
lean_dec(v___x_4369_);
v___x_4371_ = lean_nat_add(v___x_4308_, v_size_4309_);
v___x_4372_ = lean_nat_add(v___x_4371_, v_size_4327_);
lean_dec(v___x_4371_);
lean_inc_ref(v_r_4302_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 4, v_r_4302_);
lean_ctor_set(v___x_4324_, 3, v_r_4314_);
lean_ctor_set(v___x_4324_, 2, v_v_4300_);
lean_ctor_set(v___x_4324_, 1, v_k_4299_);
lean_ctor_set(v___x_4324_, 0, v___x_4372_);
v___x_4374_ = v___x_4324_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4387_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4387_, 3, v_r_4314_);
lean_ctor_set(v_reuseFailAlloc_4387_, 4, v_r_4302_);
v___x_4374_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
v_isSharedCheck_4381_ = !lean_is_exclusive(v_r_4302_);
if (v_isSharedCheck_4381_ == 0)
{
lean_object* v_unused_4382_; lean_object* v_unused_4383_; lean_object* v_unused_4384_; lean_object* v_unused_4385_; lean_object* v_unused_4386_; 
v_unused_4382_ = lean_ctor_get(v_r_4302_, 4);
lean_dec(v_unused_4382_);
v_unused_4383_ = lean_ctor_get(v_r_4302_, 3);
lean_dec(v_unused_4383_);
v_unused_4384_ = lean_ctor_get(v_r_4302_, 2);
lean_dec(v_unused_4384_);
v_unused_4385_ = lean_ctor_get(v_r_4302_, 1);
lean_dec(v_unused_4385_);
v_unused_4386_ = lean_ctor_get(v_r_4302_, 0);
lean_dec(v_unused_4386_);
v___x_4376_ = v_r_4302_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_dec(v_r_4302_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 4, v___x_4374_);
lean_ctor_set(v___x_4376_, 3, v_l_4313_);
lean_ctor_set(v___x_4376_, 2, v_v_4312_);
lean_ctor_set(v___x_4376_, 1, v_k_4311_);
lean_ctor_set(v___x_4376_, 0, v___x_4370_);
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_k_4311_);
lean_ctor_set(v_reuseFailAlloc_4380_, 2, v_v_4312_);
lean_ctor_set(v_reuseFailAlloc_4380_, 3, v_l_4313_);
lean_ctor_set(v_reuseFailAlloc_4380_, 4, v___x_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4394_; 
v_l_4394_ = lean_ctor_get(v_impl_4307_, 3);
lean_inc(v_l_4394_);
if (lean_obj_tag(v_l_4394_) == 0)
{
lean_object* v_r_4395_; lean_object* v_k_4396_; lean_object* v_v_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4408_; 
v_r_4395_ = lean_ctor_get(v_impl_4307_, 4);
v_k_4396_ = lean_ctor_get(v_impl_4307_, 1);
v_v_4397_ = lean_ctor_get(v_impl_4307_, 2);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_impl_4307_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; lean_object* v_unused_4410_; 
v_unused_4409_ = lean_ctor_get(v_impl_4307_, 3);
lean_dec(v_unused_4409_);
v_unused_4410_ = lean_ctor_get(v_impl_4307_, 0);
lean_dec(v_unused_4410_);
v___x_4399_ = v_impl_4307_;
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_r_4395_);
lean_inc(v_v_4397_);
lean_inc(v_k_4396_);
lean_dec(v_impl_4307_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4401_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4395_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 3, v_r_4395_);
lean_ctor_set(v___x_4399_, 2, v_v_4300_);
lean_ctor_set(v___x_4399_, 1, v_k_4299_);
lean_ctor_set(v___x_4399_, 0, v___x_4308_);
v___x_4403_ = v___x_4399_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_r_4395_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_r_4395_);
v___x_4403_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4405_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v___x_4403_);
lean_ctor_set(v___x_4304_, 3, v_l_4394_);
lean_ctor_set(v___x_4304_, 2, v_v_4397_);
lean_ctor_set(v___x_4304_, 1, v_k_4396_);
lean_ctor_set(v___x_4304_, 0, v___x_4401_);
v___x_4405_ = v___x_4304_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_k_4396_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_v_4397_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_l_4394_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_object* v_r_4411_; 
v_r_4411_ = lean_ctor_get(v_impl_4307_, 4);
lean_inc(v_r_4411_);
if (lean_obj_tag(v_r_4411_) == 0)
{
lean_object* v_k_4412_; lean_object* v_v_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4436_; 
v_k_4412_ = lean_ctor_get(v_impl_4307_, 1);
v_v_4413_ = lean_ctor_get(v_impl_4307_, 2);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_impl_4307_);
if (v_isSharedCheck_4436_ == 0)
{
lean_object* v_unused_4437_; lean_object* v_unused_4438_; lean_object* v_unused_4439_; 
v_unused_4437_ = lean_ctor_get(v_impl_4307_, 4);
lean_dec(v_unused_4437_);
v_unused_4438_ = lean_ctor_get(v_impl_4307_, 3);
lean_dec(v_unused_4438_);
v_unused_4439_ = lean_ctor_get(v_impl_4307_, 0);
lean_dec(v_unused_4439_);
v___x_4415_ = v_impl_4307_;
v_isShared_4416_ = v_isSharedCheck_4436_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_v_4413_);
lean_inc(v_k_4412_);
lean_dec(v_impl_4307_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4436_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v_k_4417_; lean_object* v_v_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4432_; 
v_k_4417_ = lean_ctor_get(v_r_4411_, 1);
v_v_4418_ = lean_ctor_get(v_r_4411_, 2);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_r_4411_);
if (v_isSharedCheck_4432_ == 0)
{
lean_object* v_unused_4433_; lean_object* v_unused_4434_; lean_object* v_unused_4435_; 
v_unused_4433_ = lean_ctor_get(v_r_4411_, 4);
lean_dec(v_unused_4433_);
v_unused_4434_ = lean_ctor_get(v_r_4411_, 3);
lean_dec(v_unused_4434_);
v_unused_4435_ = lean_ctor_get(v_r_4411_, 0);
lean_dec(v_unused_4435_);
v___x_4420_ = v_r_4411_;
v_isShared_4421_ = v_isSharedCheck_4432_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_v_4418_);
lean_inc(v_k_4417_);
lean_dec(v_r_4411_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4432_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4422_ = lean_unsigned_to_nat(3u);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 4, v_l_4394_);
lean_ctor_set(v___x_4420_, 3, v_l_4394_);
lean_ctor_set(v___x_4420_, 2, v_v_4413_);
lean_ctor_set(v___x_4420_, 1, v_k_4412_);
lean_ctor_set(v___x_4420_, 0, v___x_4308_);
v___x_4424_ = v___x_4420_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v_k_4412_);
lean_ctor_set(v_reuseFailAlloc_4431_, 2, v_v_4413_);
lean_ctor_set(v_reuseFailAlloc_4431_, 3, v_l_4394_);
lean_ctor_set(v_reuseFailAlloc_4431_, 4, v_l_4394_);
v___x_4424_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
lean_object* v___x_4426_; 
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 4, v_l_4394_);
lean_ctor_set(v___x_4415_, 2, v_v_4300_);
lean_ctor_set(v___x_4415_, 1, v_k_4299_);
lean_ctor_set(v___x_4415_, 0, v___x_4308_);
v___x_4426_ = v___x_4415_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4430_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4430_, 3, v_l_4394_);
lean_ctor_set(v_reuseFailAlloc_4430_, 4, v_l_4394_);
v___x_4426_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
lean_object* v___x_4428_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v___x_4426_);
lean_ctor_set(v___x_4304_, 3, v___x_4424_);
lean_ctor_set(v___x_4304_, 2, v_v_4418_);
lean_ctor_set(v___x_4304_, 1, v_k_4417_);
lean_ctor_set(v___x_4304_, 0, v___x_4422_);
v___x_4428_ = v___x_4304_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v_k_4417_);
lean_ctor_set(v_reuseFailAlloc_4429_, 2, v_v_4418_);
lean_ctor_set(v_reuseFailAlloc_4429_, 3, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4429_, 4, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4440_ = lean_unsigned_to_nat(2u);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_r_4411_);
lean_ctor_set(v___x_4304_, 3, v_impl_4307_);
lean_ctor_set(v___x_4304_, 0, v___x_4440_);
v___x_4442_ = v___x_4304_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4443_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4443_, 3, v_impl_4307_);
lean_ctor_set(v_reuseFailAlloc_4443_, 4, v_r_4411_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4445_; 
lean_dec(v_v_4300_);
lean_dec(v_k_4299_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 2, v_v_4296_);
lean_ctor_set(v___x_4304_, 1, v_k_4295_);
v___x_4445_ = v___x_4304_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_size_4298_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_k_4295_);
lean_ctor_set(v_reuseFailAlloc_4446_, 2, v_v_4296_);
lean_ctor_set(v_reuseFailAlloc_4446_, 3, v_l_4301_);
lean_ctor_set(v_reuseFailAlloc_4446_, 4, v_r_4302_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
default: 
{
lean_object* v_impl_4447_; lean_object* v___x_4448_; 
lean_dec(v_size_4298_);
v_impl_4447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4295_, v_v_4296_, v_r_4302_);
v___x_4448_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4301_) == 0)
{
lean_object* v_size_4449_; lean_object* v_size_4450_; lean_object* v_k_4451_; lean_object* v_v_4452_; lean_object* v_l_4453_; lean_object* v_r_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v_size_4449_ = lean_ctor_get(v_l_4301_, 0);
v_size_4450_ = lean_ctor_get(v_impl_4447_, 0);
lean_inc(v_size_4450_);
v_k_4451_ = lean_ctor_get(v_impl_4447_, 1);
lean_inc(v_k_4451_);
v_v_4452_ = lean_ctor_get(v_impl_4447_, 2);
lean_inc(v_v_4452_);
v_l_4453_ = lean_ctor_get(v_impl_4447_, 3);
lean_inc(v_l_4453_);
v_r_4454_ = lean_ctor_get(v_impl_4447_, 4);
lean_inc(v_r_4454_);
v___x_4455_ = lean_unsigned_to_nat(3u);
v___x_4456_ = lean_nat_mul(v___x_4455_, v_size_4449_);
v___x_4457_ = lean_nat_dec_lt(v___x_4456_, v_size_4450_);
lean_dec(v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4461_; 
lean_dec(v_r_4454_);
lean_dec(v_l_4453_);
lean_dec(v_v_4452_);
lean_dec(v_k_4451_);
v___x_4458_ = lean_nat_add(v___x_4448_, v_size_4449_);
v___x_4459_ = lean_nat_add(v___x_4458_, v_size_4450_);
lean_dec(v_size_4450_);
lean_dec(v___x_4458_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_impl_4447_);
lean_ctor_set(v___x_4304_, 0, v___x_4459_);
v___x_4461_ = v___x_4304_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4462_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4462_, 3, v_l_4301_);
lean_ctor_set(v_reuseFailAlloc_4462_, 4, v_impl_4447_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
else
{
lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4526_; 
v_isSharedCheck_4526_ = !lean_is_exclusive(v_impl_4447_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; lean_object* v_unused_4528_; lean_object* v_unused_4529_; lean_object* v_unused_4530_; lean_object* v_unused_4531_; 
v_unused_4527_ = lean_ctor_get(v_impl_4447_, 4);
lean_dec(v_unused_4527_);
v_unused_4528_ = lean_ctor_get(v_impl_4447_, 3);
lean_dec(v_unused_4528_);
v_unused_4529_ = lean_ctor_get(v_impl_4447_, 2);
lean_dec(v_unused_4529_);
v_unused_4530_ = lean_ctor_get(v_impl_4447_, 1);
lean_dec(v_unused_4530_);
v_unused_4531_ = lean_ctor_get(v_impl_4447_, 0);
lean_dec(v_unused_4531_);
v___x_4464_ = v_impl_4447_;
v_isShared_4465_ = v_isSharedCheck_4526_;
goto v_resetjp_4463_;
}
else
{
lean_dec(v_impl_4447_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4526_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v_size_4466_; lean_object* v_k_4467_; lean_object* v_v_4468_; lean_object* v_l_4469_; lean_object* v_r_4470_; lean_object* v_size_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; uint8_t v___x_4474_; 
v_size_4466_ = lean_ctor_get(v_l_4453_, 0);
v_k_4467_ = lean_ctor_get(v_l_4453_, 1);
v_v_4468_ = lean_ctor_get(v_l_4453_, 2);
v_l_4469_ = lean_ctor_get(v_l_4453_, 3);
v_r_4470_ = lean_ctor_get(v_l_4453_, 4);
v_size_4471_ = lean_ctor_get(v_r_4454_, 0);
v___x_4472_ = lean_unsigned_to_nat(2u);
v___x_4473_ = lean_nat_mul(v___x_4472_, v_size_4471_);
v___x_4474_ = lean_nat_dec_lt(v_size_4466_, v___x_4473_);
lean_dec(v___x_4473_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4502_; 
lean_inc(v_r_4470_);
lean_inc(v_l_4469_);
lean_inc(v_v_4468_);
lean_inc(v_k_4467_);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_l_4453_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; lean_object* v_unused_4504_; lean_object* v_unused_4505_; lean_object* v_unused_4506_; lean_object* v_unused_4507_; 
v_unused_4503_ = lean_ctor_get(v_l_4453_, 4);
lean_dec(v_unused_4503_);
v_unused_4504_ = lean_ctor_get(v_l_4453_, 3);
lean_dec(v_unused_4504_);
v_unused_4505_ = lean_ctor_get(v_l_4453_, 2);
lean_dec(v_unused_4505_);
v_unused_4506_ = lean_ctor_get(v_l_4453_, 1);
lean_dec(v_unused_4506_);
v_unused_4507_ = lean_ctor_get(v_l_4453_, 0);
lean_dec(v_unused_4507_);
v___x_4476_ = v_l_4453_;
v_isShared_4477_ = v_isSharedCheck_4502_;
goto v_resetjp_4475_;
}
else
{
lean_dec(v_l_4453_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4502_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4492_; 
v___x_4478_ = lean_nat_add(v___x_4448_, v_size_4449_);
v___x_4479_ = lean_nat_add(v___x_4478_, v_size_4450_);
lean_dec(v_size_4450_);
if (lean_obj_tag(v_l_4469_) == 0)
{
lean_object* v_size_4500_; 
v_size_4500_ = lean_ctor_get(v_l_4469_, 0);
lean_inc(v_size_4500_);
v___y_4492_ = v_size_4500_;
goto v___jp_4491_;
}
else
{
lean_object* v___x_4501_; 
v___x_4501_ = lean_unsigned_to_nat(0u);
v___y_4492_ = v___x_4501_;
goto v___jp_4491_;
}
v___jp_4480_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = lean_nat_add(v___y_4481_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec(v___y_4481_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 4, v_r_4454_);
lean_ctor_set(v___x_4476_, 3, v_r_4470_);
lean_ctor_set(v___x_4476_, 2, v_v_4452_);
lean_ctor_set(v___x_4476_, 1, v_k_4451_);
lean_ctor_set(v___x_4476_, 0, v___x_4484_);
v___x_4486_ = v___x_4476_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_k_4451_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_v_4452_);
lean_ctor_set(v_reuseFailAlloc_4490_, 3, v_r_4470_);
lean_ctor_set(v_reuseFailAlloc_4490_, 4, v_r_4454_);
v___x_4486_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4488_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 4, v___x_4486_);
lean_ctor_set(v___x_4464_, 3, v___y_4482_);
lean_ctor_set(v___x_4464_, 2, v_v_4468_);
lean_ctor_set(v___x_4464_, 1, v_k_4467_);
lean_ctor_set(v___x_4464_, 0, v___x_4479_);
v___x_4488_ = v___x_4464_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v_k_4467_);
lean_ctor_set(v_reuseFailAlloc_4489_, 2, v_v_4468_);
lean_ctor_set(v_reuseFailAlloc_4489_, 3, v___y_4482_);
lean_ctor_set(v_reuseFailAlloc_4489_, 4, v___x_4486_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
v___jp_4491_:
{
lean_object* v___x_4493_; lean_object* v___x_4495_; 
v___x_4493_ = lean_nat_add(v___x_4478_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec(v___x_4478_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_l_4469_);
lean_ctor_set(v___x_4304_, 0, v___x_4493_);
v___x_4495_ = v___x_4304_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v_l_4301_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v_l_4469_);
v___x_4495_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_nat_add(v___x_4448_, v_size_4471_);
if (lean_obj_tag(v_r_4470_) == 0)
{
lean_object* v_size_4497_; 
v_size_4497_ = lean_ctor_get(v_r_4470_, 0);
lean_inc(v_size_4497_);
v___y_4481_ = v___x_4496_;
v___y_4482_ = v___x_4495_;
v___y_4483_ = v_size_4497_;
goto v___jp_4480_;
}
else
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_unsigned_to_nat(0u);
v___y_4481_ = v___x_4496_;
v___y_4482_ = v___x_4495_;
v___y_4483_ = v___x_4498_;
goto v___jp_4480_;
}
}
}
}
}
else
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
lean_del_object(v___x_4304_);
v___x_4508_ = lean_nat_add(v___x_4448_, v_size_4449_);
v___x_4509_ = lean_nat_add(v___x_4508_, v_size_4450_);
lean_dec(v_size_4450_);
v___x_4510_ = lean_nat_add(v___x_4508_, v_size_4466_);
lean_dec(v___x_4508_);
lean_inc_ref(v_l_4301_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 4, v_l_4453_);
lean_ctor_set(v___x_4464_, 3, v_l_4301_);
lean_ctor_set(v___x_4464_, 2, v_v_4300_);
lean_ctor_set(v___x_4464_, 1, v_k_4299_);
lean_ctor_set(v___x_4464_, 0, v___x_4510_);
v___x_4512_ = v___x_4464_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4525_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4525_, 3, v_l_4301_);
lean_ctor_set(v_reuseFailAlloc_4525_, 4, v_l_4453_);
v___x_4512_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_isSharedCheck_4519_ = !lean_is_exclusive(v_l_4301_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; lean_object* v_unused_4521_; lean_object* v_unused_4522_; lean_object* v_unused_4523_; lean_object* v_unused_4524_; 
v_unused_4520_ = lean_ctor_get(v_l_4301_, 4);
lean_dec(v_unused_4520_);
v_unused_4521_ = lean_ctor_get(v_l_4301_, 3);
lean_dec(v_unused_4521_);
v_unused_4522_ = lean_ctor_get(v_l_4301_, 2);
lean_dec(v_unused_4522_);
v_unused_4523_ = lean_ctor_get(v_l_4301_, 1);
lean_dec(v_unused_4523_);
v_unused_4524_ = lean_ctor_get(v_l_4301_, 0);
lean_dec(v_unused_4524_);
v___x_4514_ = v_l_4301_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_dec(v_l_4301_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 4, v_r_4454_);
lean_ctor_set(v___x_4514_, 3, v___x_4512_);
lean_ctor_set(v___x_4514_, 2, v_v_4452_);
lean_ctor_set(v___x_4514_, 1, v_k_4451_);
lean_ctor_set(v___x_4514_, 0, v___x_4509_);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4509_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_k_4451_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_v_4452_);
lean_ctor_set(v_reuseFailAlloc_4518_, 3, v___x_4512_);
lean_ctor_set(v_reuseFailAlloc_4518_, 4, v_r_4454_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4532_; 
v_l_4532_ = lean_ctor_get(v_impl_4447_, 3);
lean_inc(v_l_4532_);
if (lean_obj_tag(v_l_4532_) == 0)
{
lean_object* v_r_4533_; lean_object* v_k_4534_; lean_object* v_v_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4558_; 
v_r_4533_ = lean_ctor_get(v_impl_4447_, 4);
v_k_4534_ = lean_ctor_get(v_impl_4447_, 1);
v_v_4535_ = lean_ctor_get(v_impl_4447_, 2);
v_isSharedCheck_4558_ = !lean_is_exclusive(v_impl_4447_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; lean_object* v_unused_4560_; 
v_unused_4559_ = lean_ctor_get(v_impl_4447_, 3);
lean_dec(v_unused_4559_);
v_unused_4560_ = lean_ctor_get(v_impl_4447_, 0);
lean_dec(v_unused_4560_);
v___x_4537_ = v_impl_4447_;
v_isShared_4538_ = v_isSharedCheck_4558_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_r_4533_);
lean_inc(v_v_4535_);
lean_inc(v_k_4534_);
lean_dec(v_impl_4447_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4558_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v_k_4539_; lean_object* v_v_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4554_; 
v_k_4539_ = lean_ctor_get(v_l_4532_, 1);
v_v_4540_ = lean_ctor_get(v_l_4532_, 2);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_l_4532_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; lean_object* v_unused_4556_; lean_object* v_unused_4557_; 
v_unused_4555_ = lean_ctor_get(v_l_4532_, 4);
lean_dec(v_unused_4555_);
v_unused_4556_ = lean_ctor_get(v_l_4532_, 3);
lean_dec(v_unused_4556_);
v_unused_4557_ = lean_ctor_get(v_l_4532_, 0);
lean_dec(v_unused_4557_);
v___x_4542_ = v_l_4532_;
v_isShared_4543_ = v_isSharedCheck_4554_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_v_4540_);
lean_inc(v_k_4539_);
lean_dec(v_l_4532_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4554_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4544_; lean_object* v___x_4546_; 
v___x_4544_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4533_, 2);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 4, v_r_4533_);
lean_ctor_set(v___x_4542_, 3, v_r_4533_);
lean_ctor_set(v___x_4542_, 2, v_v_4300_);
lean_ctor_set(v___x_4542_, 1, v_k_4299_);
lean_ctor_set(v___x_4542_, 0, v___x_4448_);
v___x_4546_ = v___x_4542_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4553_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4553_, 3, v_r_4533_);
lean_ctor_set(v_reuseFailAlloc_4553_, 4, v_r_4533_);
v___x_4546_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4548_; 
lean_inc(v_r_4533_);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 3, v_r_4533_);
lean_ctor_set(v___x_4537_, 0, v___x_4448_);
v___x_4548_ = v___x_4537_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4552_, 1, v_k_4534_);
lean_ctor_set(v_reuseFailAlloc_4552_, 2, v_v_4535_);
lean_ctor_set(v_reuseFailAlloc_4552_, 3, v_r_4533_);
lean_ctor_set(v_reuseFailAlloc_4552_, 4, v_r_4533_);
v___x_4548_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4550_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v___x_4548_);
lean_ctor_set(v___x_4304_, 3, v___x_4546_);
lean_ctor_set(v___x_4304_, 2, v_v_4540_);
lean_ctor_set(v___x_4304_, 1, v_k_4539_);
lean_ctor_set(v___x_4304_, 0, v___x_4544_);
v___x_4550_ = v___x_4304_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4544_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_k_4539_);
lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_v_4540_);
lean_ctor_set(v_reuseFailAlloc_4551_, 3, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4551_, 4, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
}
}
else
{
lean_object* v_r_4561_; 
v_r_4561_ = lean_ctor_get(v_impl_4447_, 4);
lean_inc(v_r_4561_);
if (lean_obj_tag(v_r_4561_) == 0)
{
lean_object* v_k_4562_; lean_object* v_v_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4574_; 
v_k_4562_ = lean_ctor_get(v_impl_4447_, 1);
v_v_4563_ = lean_ctor_get(v_impl_4447_, 2);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_impl_4447_);
if (v_isSharedCheck_4574_ == 0)
{
lean_object* v_unused_4575_; lean_object* v_unused_4576_; lean_object* v_unused_4577_; 
v_unused_4575_ = lean_ctor_get(v_impl_4447_, 4);
lean_dec(v_unused_4575_);
v_unused_4576_ = lean_ctor_get(v_impl_4447_, 3);
lean_dec(v_unused_4576_);
v_unused_4577_ = lean_ctor_get(v_impl_4447_, 0);
lean_dec(v_unused_4577_);
v___x_4565_ = v_impl_4447_;
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_v_4563_);
lean_inc(v_k_4562_);
lean_dec(v_impl_4447_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4567_ = lean_unsigned_to_nat(3u);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 4, v_l_4532_);
lean_ctor_set(v___x_4565_, 2, v_v_4300_);
lean_ctor_set(v___x_4565_, 1, v_k_4299_);
lean_ctor_set(v___x_4565_, 0, v___x_4448_);
v___x_4569_ = v___x_4565_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4573_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4573_, 3, v_l_4532_);
lean_ctor_set(v_reuseFailAlloc_4573_, 4, v_l_4532_);
v___x_4569_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4571_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_r_4561_);
lean_ctor_set(v___x_4304_, 3, v___x_4569_);
lean_ctor_set(v___x_4304_, 2, v_v_4563_);
lean_ctor_set(v___x_4304_, 1, v_k_4562_);
lean_ctor_set(v___x_4304_, 0, v___x_4567_);
v___x_4571_ = v___x_4304_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4572_, 3, v___x_4569_);
lean_ctor_set(v_reuseFailAlloc_4572_, 4, v_r_4561_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4578_ = lean_unsigned_to_nat(2u);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_impl_4447_);
lean_ctor_set(v___x_4304_, 3, v_r_4561_);
lean_ctor_set(v___x_4304_, 0, v___x_4578_);
v___x_4580_ = v___x_4304_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4581_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4581_, 3, v_r_4561_);
lean_ctor_set(v_reuseFailAlloc_4581_, 4, v_impl_4447_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4583_ = lean_unsigned_to_nat(1u);
v___x_4584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
lean_ctor_set(v___x_4584_, 1, v_k_4295_);
lean_ctor_set(v___x_4584_, 2, v_v_4296_);
lean_ctor_set(v___x_4584_, 3, v_t_4297_);
lean_ctor_set(v___x_4584_, 4, v_t_4297_);
return v___x_4584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4585_, lean_object* v_k_4586_){
_start:
{
if (lean_obj_tag(v_t_4585_) == 0)
{
lean_object* v_k_4587_; lean_object* v_v_4588_; lean_object* v_l_4589_; lean_object* v_r_4590_; uint8_t v___x_4591_; 
v_k_4587_ = lean_ctor_get(v_t_4585_, 1);
v_v_4588_ = lean_ctor_get(v_t_4585_, 2);
v_l_4589_ = lean_ctor_get(v_t_4585_, 3);
v_r_4590_ = lean_ctor_get(v_t_4585_, 4);
v___x_4591_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4586_, v_k_4587_);
switch(v___x_4591_)
{
case 0:
{
v_t_4585_ = v_l_4589_;
goto _start;
}
case 1:
{
lean_object* v___x_4593_; 
lean_inc(v_v_4588_);
v___x_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4593_, 0, v_v_4588_);
return v___x_4593_;
}
default: 
{
v_t_4585_ = v_r_4590_;
goto _start;
}
}
}
else
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_box(0);
return v___x_4595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4596_, lean_object* v_k_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4596_, v_k_4597_);
lean_dec(v_k_4597_);
lean_dec(v_t_4596_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4599_, lean_object* v_k_4600_, lean_object* v_v_4601_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4599_, v_k_4600_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4603_ = lean_box(0);
v___x_4604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4604_, 0, v_v_4601_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4600_, v___x_4604_, v_map_4599_);
return v___x_4605_;
}
else
{
lean_object* v_val_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v_val_4606_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_val_4606_);
lean_dec_ref(v___x_4602_);
v___x_4607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4607_, 0, v_v_4601_);
lean_ctor_set(v___x_4607_, 1, v_val_4606_);
v___x_4608_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4600_, v___x_4607_, v_map_4599_);
return v___x_4608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4609_, lean_object* v_map_4610_, lean_object* v_k_4611_, lean_object* v_v_4612_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4610_, v_k_4611_, v_v_4612_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4614_, lean_object* v_t_4615_, lean_object* v_k_4616_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4615_, v_k_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4618_, lean_object* v_t_4619_, lean_object* v_k_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4618_, v_t_4619_, v_k_4620_);
lean_dec(v_k_4620_);
lean_dec(v_t_4619_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4622_, lean_object* v_k_4623_, lean_object* v_v_4624_, lean_object* v_t_4625_, lean_object* v_hl_4626_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4623_, v_v_4624_, v_t_4625_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4628_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_box(1);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_box(1);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4632_){
_start:
{
lean_object* v___f_4633_; 
v___f_4633_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4633_, 0, v_inst_4632_);
return v___f_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4634_, lean_object* v_00_u03b1_4635_, lean_object* v_inst_4636_){
_start:
{
lean_object* v___f_4637_; 
v___f_4637_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4637_, 0, v_inst_4636_);
return v___f_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t v_x_4642_){
_start:
{
switch(v_x_4642_)
{
case 0:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_unsigned_to_nat(0u);
return v___x_4643_;
}
case 1:
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_unsigned_to_nat(1u);
return v___x_4644_;
}
default: 
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_unsigned_to_nat(2u);
return v___x_4645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object* v_x_4646_){
_start:
{
uint8_t v_x_boxed_4647_; lean_object* v_res_4648_; 
v_x_boxed_4647_ = lean_unbox(v_x_4646_);
v_res_4648_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_boxed_4647_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t v_x_4649_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4649_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object* v_x_4651_){
_start:
{
uint8_t v_x_4__boxed_4652_; lean_object* v_res_4653_; 
v_x_4__boxed_4652_ = lean_unbox(v_x_4651_);
v_res_4653_ = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(v_x_4__boxed_4652_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4654_){
_start:
{
lean_inc(v_k_4654_);
return v_k_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4655_);
lean_dec(v_k_4655_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4657_, lean_object* v_ctorIdx_4658_, uint8_t v_t_4659_, lean_object* v_h_4660_, lean_object* v_k_4661_){
_start:
{
lean_inc(v_k_4661_);
return v_k_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4662_, lean_object* v_ctorIdx_4663_, lean_object* v_t_4664_, lean_object* v_h_4665_, lean_object* v_k_4666_){
_start:
{
uint8_t v_t_boxed_4667_; lean_object* v_res_4668_; 
v_t_boxed_4667_ = lean_unbox(v_t_4664_);
v_res_4668_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4662_, v_ctorIdx_4663_, v_t_boxed_4667_, v_h_4665_, v_k_4666_);
lean_dec(v_k_4666_);
lean_dec(v_ctorIdx_4663_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4669_){
_start:
{
lean_inc(v_default_4669_);
return v_default_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4670_);
lean_dec(v_default_4670_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4672_, uint8_t v_t_4673_, lean_object* v_h_4674_, lean_object* v_default_4675_){
_start:
{
lean_inc(v_default_4675_);
return v_default_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4676_, lean_object* v_t_4677_, lean_object* v_h_4678_, lean_object* v_default_4679_){
_start:
{
uint8_t v_t_boxed_4680_; lean_object* v_res_4681_; 
v_t_boxed_4680_ = lean_unbox(v_t_4677_);
v_res_4681_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4676_, v_t_boxed_4680_, v_h_4678_, v_default_4679_);
lean_dec(v_default_4679_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4682_){
_start:
{
lean_inc(v_symbol_4682_);
return v_symbol_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4683_);
lean_dec(v_symbol_4683_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4685_, uint8_t v_t_4686_, lean_object* v_h_4687_, lean_object* v_symbol_4688_){
_start:
{
lean_inc(v_symbol_4688_);
return v_symbol_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4689_, lean_object* v_t_4690_, lean_object* v_h_4691_, lean_object* v_symbol_4692_){
_start:
{
uint8_t v_t_boxed_4693_; lean_object* v_res_4694_; 
v_t_boxed_4693_ = lean_unbox(v_t_4690_);
v_res_4694_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4689_, v_t_boxed_4693_, v_h_4691_, v_symbol_4692_);
lean_dec(v_symbol_4692_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4695_){
_start:
{
lean_inc(v_both_4695_);
return v_both_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4696_);
lean_dec(v_both_4696_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4698_, uint8_t v_t_4699_, lean_object* v_h_4700_, lean_object* v_both_4701_){
_start:
{
lean_inc(v_both_4701_);
return v_both_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4702_, lean_object* v_t_4703_, lean_object* v_h_4704_, lean_object* v_both_4705_){
_start:
{
uint8_t v_t_boxed_4706_; lean_object* v_res_4707_; 
v_t_boxed_4706_ = lean_unbox(v_t_4703_);
v_res_4707_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4702_, v_t_boxed_4706_, v_h_4704_, v_both_4705_);
lean_dec(v_both_4705_);
return v_res_4707_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4708_; 
v___x_4708_ = 0;
return v___x_4708_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4709_; 
v___x_4709_ = 0;
return v___x_4709_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4710_, uint8_t v_y_4711_){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4712_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4710_);
v___x_4713_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_y_4711_);
v___x_4714_ = lean_nat_dec_eq(v___x_4712_, v___x_4713_);
lean_dec(v___x_4713_);
lean_dec(v___x_4712_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4715_, lean_object* v_y_4716_){
_start:
{
uint8_t v_x_17__boxed_4717_; uint8_t v_y_18__boxed_4718_; uint8_t v_res_4719_; lean_object* v_r_4720_; 
v_x_17__boxed_4717_ = lean_unbox(v_x_4715_);
v_y_18__boxed_4718_ = lean_unbox(v_y_4716_);
v_res_4719_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_17__boxed_4717_, v_y_18__boxed_4718_);
v_r_4720_ = lean_box(v_res_4719_);
return v_r_4720_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = lean_unsigned_to_nat(2u);
v___x_4733_ = lean_nat_to_int(v___x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4734_, lean_object* v_prec_4735_){
_start:
{
lean_object* v___y_4737_; lean_object* v___y_4744_; lean_object* v___y_4751_; 
switch(v_x_4734_)
{
case 0:
{
lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4757_ = lean_unsigned_to_nat(1024u);
v___x_4758_ = lean_nat_dec_le(v___x_4757_, v_prec_4735_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4737_ = v___x_4759_;
goto v___jp_4736_;
}
else
{
lean_object* v___x_4760_; 
v___x_4760_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4737_ = v___x_4760_;
goto v___jp_4736_;
}
}
case 1:
{
lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = lean_unsigned_to_nat(1024u);
v___x_4762_ = lean_nat_dec_le(v___x_4761_, v_prec_4735_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4744_ = v___x_4763_;
goto v___jp_4743_;
}
else
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4744_ = v___x_4764_;
goto v___jp_4743_;
}
}
default: 
{
lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = lean_unsigned_to_nat(1024u);
v___x_4766_ = lean_nat_dec_le(v___x_4765_, v_prec_4735_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; 
v___x_4767_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4751_ = v___x_4767_;
goto v___jp_4750_;
}
else
{
lean_object* v___x_4768_; 
v___x_4768_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4751_ = v___x_4768_;
goto v___jp_4750_;
}
}
}
v___jp_4736_:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4738_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
v___x_4739_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___y_4737_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
v___x_4740_ = 0;
v___x_4741_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4741_, 0, v___x_4739_);
lean_ctor_set_uint8(v___x_4741_, sizeof(void*)*1, v___x_4740_);
v___x_4742_ = l_Repr_addAppParen(v___x_4741_, v_prec_4735_);
return v___x_4742_;
}
v___jp_4743_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
v___x_4745_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
v___x_4746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4746_, 0, v___y_4744_);
lean_ctor_set(v___x_4746_, 1, v___x_4745_);
v___x_4747_ = 0;
v___x_4748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4748_, 0, v___x_4746_);
lean_ctor_set_uint8(v___x_4748_, sizeof(void*)*1, v___x_4747_);
v___x_4749_ = l_Repr_addAppParen(v___x_4748_, v_prec_4735_);
return v___x_4749_;
}
v___jp_4750_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4752_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
v___x_4753_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4753_, 0, v___y_4751_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = 0;
v___x_4755_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4755_, 0, v___x_4753_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*1, v___x_4754_);
v___x_4756_ = l_Repr_addAppParen(v___x_4755_, v_prec_4735_);
return v___x_4756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_4769_, lean_object* v_prec_4770_){
_start:
{
uint8_t v_x_175__boxed_4771_; lean_object* v_res_4772_; 
v_x_175__boxed_4771_ = lean_unbox(v_x_4769_);
v_res_4772_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_175__boxed_4771_, v_prec_4770_);
lean_dec(v_prec_4770_);
return v_res_4772_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4775_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4778_ = 0;
v___x_4779_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_4780_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_4781_ = lean_box(0);
v___x_4782_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
lean_ctor_set(v___x_4782_, 1, v___x_4780_);
lean_ctor_set(v___x_4782_, 2, v___x_4779_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*3, v___x_4778_);
return v___x_4782_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_4783_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_4785_, lean_object* v_c_4786_, lean_object* v_s_4787_, uint8_t v_behavior_4788_){
_start:
{
lean_object* v___x_4789_; lean_object* v_fst_4790_; lean_object* v_snd_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4833_; 
v___x_4789_ = l_Lean_Parser_peekToken(v_c_4786_, v_s_4787_);
v_fst_4790_ = lean_ctor_get(v___x_4789_, 0);
v_snd_4791_ = lean_ctor_get(v___x_4789_, 1);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4793_ = v___x_4789_;
v_isShared_4794_ = v_isSharedCheck_4833_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_snd_4791_);
lean_inc(v_fst_4790_);
lean_dec(v___x_4789_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4833_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_n_4796_; 
if (lean_obj_tag(v_snd_4791_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
lean_del_object(v___x_4793_);
lean_dec(v_fst_4790_);
v_a_4808_ = lean_ctor_get(v_snd_4791_, 0);
lean_inc(v_a_4808_);
lean_dec_ref(v_snd_4791_);
v___x_4809_ = lean_box(0);
v___x_4810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4810_, 0, v_a_4808_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
return v___x_4810_;
}
else
{
lean_object* v_a_4811_; 
v_a_4811_ = lean_ctor_get(v_snd_4791_, 0);
lean_inc(v_a_4811_);
lean_dec_ref(v_snd_4791_);
switch(lean_obj_tag(v_a_4811_))
{
case 2:
{
lean_object* v_val_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v_val_4812_ = lean_ctor_get(v_a_4811_, 1);
lean_inc_ref(v_val_4812_);
lean_dec_ref(v_a_4811_);
v___x_4813_ = lean_box(0);
v___x_4814_ = l_Lean_Name_str___override(v___x_4813_, v_val_4812_);
v_n_4796_ = v___x_4814_;
goto v___jp_4795_;
}
case 3:
{
switch(v_behavior_4788_)
{
case 0:
{
lean_dec_ref(v_a_4811_);
goto v___jp_4806_;
}
case 1:
{
lean_object* v_val_4815_; lean_object* v___x_4816_; 
v_val_4815_ = lean_ctor_get(v_a_4811_, 2);
lean_inc(v_val_4815_);
lean_dec_ref(v_a_4811_);
v___x_4816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4785_, v_val_4815_);
lean_dec(v_val_4815_);
if (lean_obj_tag(v___x_4816_) == 0)
{
goto v___jp_4806_;
}
else
{
lean_object* v_val_4817_; lean_object* v___x_4818_; 
lean_del_object(v___x_4793_);
v_val_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_val_4817_);
lean_dec_ref(v___x_4816_);
v___x_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4818_, 0, v_fst_4790_);
lean_ctor_set(v___x_4818_, 1, v_val_4817_);
return v___x_4818_;
}
}
default: 
{
lean_object* v_val_4819_; lean_object* v___x_4820_; 
v_val_4819_ = lean_ctor_get(v_a_4811_, 2);
lean_inc(v_val_4819_);
lean_dec_ref(v_a_4811_);
v___x_4820_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4785_, v_val_4819_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_dec(v_val_4819_);
goto v___jp_4806_;
}
else
{
lean_object* v_val_4821_; lean_object* v___x_4822_; uint8_t v___x_4823_; 
lean_del_object(v___x_4793_);
v_val_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_val_4821_);
lean_dec_ref(v___x_4820_);
v___x_4822_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_4823_ = lean_name_eq(v_val_4819_, v___x_4822_);
lean_dec(v_val_4819_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; 
v___x_4824_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4785_, v___x_4822_);
if (lean_obj_tag(v___x_4824_) == 1)
{
lean_object* v_val_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v_val_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_val_4825_);
lean_dec_ref(v___x_4824_);
v___x_4826_ = l_List_appendTR___redArg(v_val_4821_, v_val_4825_);
v___x_4827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4827_, 0, v_fst_4790_);
lean_ctor_set(v___x_4827_, 1, v___x_4826_);
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; 
lean_dec(v___x_4824_);
v___x_4828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4828_, 0, v_fst_4790_);
lean_ctor_set(v___x_4828_, 1, v_val_4821_);
return v___x_4828_;
}
}
else
{
lean_object* v___x_4829_; 
v___x_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4829_, 0, v_fst_4790_);
lean_ctor_set(v___x_4829_, 1, v_val_4821_);
return v___x_4829_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_4830_; 
v_kind_4830_ = lean_ctor_get(v_a_4811_, 1);
lean_inc(v_kind_4830_);
lean_dec_ref(v_a_4811_);
v_n_4796_ = v_kind_4830_;
goto v___jp_4795_;
}
default: 
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
lean_dec(v_a_4811_);
lean_del_object(v___x_4793_);
v___x_4831_ = lean_box(0);
v___x_4832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4832_, 0, v_fst_4790_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
return v___x_4832_;
}
}
}
v___jp_4795_:
{
lean_object* v___x_4797_; 
v___x_4797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4785_, v_n_4796_);
lean_dec(v_n_4796_);
if (lean_obj_tag(v___x_4797_) == 1)
{
lean_object* v_val_4798_; lean_object* v___x_4800_; 
v_val_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_val_4798_);
lean_dec_ref(v___x_4797_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 1, v_val_4798_);
v___x_4800_ = v___x_4793_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_fst_4790_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_val_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4804_; 
lean_dec(v___x_4797_);
v___x_4802_ = lean_box(0);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 1, v___x_4802_);
v___x_4804_ = v___x_4793_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_fst_4790_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
v___jp_4806_:
{
lean_object* v___x_4807_; 
v___x_4807_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_4796_ = v___x_4807_;
goto v___jp_4795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_4834_, lean_object* v_c_4835_, lean_object* v_s_4836_, lean_object* v_behavior_4837_){
_start:
{
uint8_t v_behavior_boxed_4838_; lean_object* v_res_4839_; 
v_behavior_boxed_4838_ = lean_unbox(v_behavior_4837_);
v_res_4839_ = l_Lean_Parser_indexed___redArg(v_map_4834_, v_c_4835_, v_s_4836_, v_behavior_boxed_4838_);
lean_dec(v_map_4834_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_4840_, lean_object* v_map_4841_, lean_object* v_c_4842_, lean_object* v_s_4843_, uint8_t v_behavior_4844_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l_Lean_Parser_indexed___redArg(v_map_4841_, v_c_4842_, v_s_4843_, v_behavior_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_4846_, lean_object* v_map_4847_, lean_object* v_c_4848_, lean_object* v_s_4849_, lean_object* v_behavior_4850_){
_start:
{
uint8_t v_behavior_boxed_4851_; lean_object* v_res_4852_; 
v_behavior_boxed_4851_ = lean_unbox(v_behavior_4850_);
v_res_4852_ = l_Lean_Parser_indexed(v_00_u03b1_4846_, v_map_4847_, v_c_4848_, v_s_4849_, v_behavior_boxed_4851_);
lean_dec(v_map_4847_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l_Lean_Parser_whitespace(v___y_4854_, v___y_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_4857_, v___y_4858_, v___y_4859_);
lean_dec(v_x_4857_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___f_4863_ = ((lean_object*)(l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_4864_ = lean_st_mk_ref(v___f_4863_);
v___x_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_4868_){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4870_ = lean_st_ref_get(v___x_4868_);
v___x_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_4872_);
lean_dec(v___x_4872_);
return v_res_4874_;
}
}
static lean_object* _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___f_4876_; 
v___x_4875_ = l_Lean_Parser_categoryParserFnRef;
v___f_4876_ = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4876_, 0, v___x_4875_);
return v___f_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___f_4878_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_4879_ = lean_box(0);
v___x_4880_ = lean_box(2);
v___x_4881_ = l_Lean_registerEnvExtension___redArg(v___f_4878_, v___x_4879_, v___x_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_4885_, v___y_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_4888_, v___y_4889_, v___y_4890_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v_a_4888_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_4895_, lean_object* v_ctx_4896_, lean_object* v_s_4897_){
_start:
{
lean_object* v_toParserModuleContext_4898_; lean_object* v_env_4899_; lean_object* v___x_4900_; lean_object* v_asyncMode_4901_; lean_object* v___f_4902_; lean_object* v___x_4903_; lean_object* v___x_11__overap_4904_; lean_object* v___x_4905_; 
v_toParserModuleContext_4898_ = lean_ctor_get(v_ctx_4896_, 1);
v_env_4899_ = lean_ctor_get(v_toParserModuleContext_4898_, 0);
v___x_4900_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_4901_ = lean_ctor_get(v___x_4900_, 2);
lean_inc(v_asyncMode_4901_);
v___f_4902_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_4903_ = lean_box(0);
lean_inc_ref(v_env_4899_);
v___x_11__overap_4904_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_4902_, v___x_4900_, v_env_4899_, v_asyncMode_4901_, v___x_4903_);
lean_dec(v_asyncMode_4901_);
v___x_4905_ = lean_apply_3(v___x_11__overap_4904_, v_catName_4895_, v_ctx_4896_, v_s_4897_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_4906_, lean_object* v_x_4907_){
_start:
{
lean_object* v_quotDepth_4908_; uint8_t v_suppressInsideQuot_4909_; lean_object* v_savedPos_x3f_4910_; lean_object* v_forbiddenTk_x3f_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
v_quotDepth_4908_ = lean_ctor_get(v_x_4907_, 1);
v_suppressInsideQuot_4909_ = lean_ctor_get_uint8(v_x_4907_, sizeof(void*)*4);
v_savedPos_x3f_4910_ = lean_ctor_get(v_x_4907_, 2);
v_forbiddenTk_x3f_4911_ = lean_ctor_get(v_x_4907_, 3);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_x_4907_);
if (v_isSharedCheck_4918_ == 0)
{
lean_object* v_unused_4919_; 
v_unused_4919_ = lean_ctor_get(v_x_4907_, 0);
lean_dec(v_unused_4919_);
v___x_4913_ = v_x_4907_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4911_);
lean_inc(v_savedPos_x3f_4910_);
lean_inc(v_quotDepth_4908_);
lean_dec(v_x_4907_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v_prec_4906_);
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_prec_4906_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_quotDepth_4908_);
lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_savedPos_x3f_4910_);
lean_ctor_set(v_reuseFailAlloc_4917_, 3, v_forbiddenTk_x3f_4911_);
lean_ctor_set_uint8(v_reuseFailAlloc_4917_, sizeof(void*)*4, v_suppressInsideQuot_4909_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_4920_, lean_object* v_prec_4921_){
_start:
{
lean_object* v___f_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___f_4922_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_4922_, 0, v_prec_4921_);
v___x_4923_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_4920_);
v___x_4924_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_4924_, 0, v_catName_4920_);
v___x_4925_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_4925_, 0, v_catName_4920_);
lean_closure_set(v___x_4925_, 1, v___x_4924_);
v___x_4926_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_4926_, 0, v___f_4922_);
lean_closure_set(v___x_4926_, 1, v___x_4925_);
v___x_4927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4923_);
lean_ctor_set(v___x_4927_, 1, v___x_4926_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_4931_){
_start:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_4933_ = l_Lean_Parser_categoryParser(v___x_4932_, v_prec_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_4935_, lean_object* v_s_4936_){
_start:
{
lean_object* v_stxStack_4937_; lean_object* v_pos_4938_; lean_object* v_prev_4939_; uint8_t v___x_4940_; 
v_stxStack_4937_ = lean_ctor_get(v_s_4936_, 0);
v_pos_4938_ = lean_ctor_get(v_s_4936_, 2);
v_prev_4939_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4937_);
v___x_4940_ = l_Lean_Parser_checkTailNoWs(v_prev_4939_);
lean_dec(v_prev_4939_);
if (v___x_4940_ == 0)
{
return v_s_4936_;
}
else
{
lean_object* v_toInputContext_4941_; uint8_t v___x_4942_; 
v_toInputContext_4941_ = lean_ctor_get(v_c_4935_, 0);
v___x_4942_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4941_, v_pos_4938_);
if (v___x_4942_ == 0)
{
lean_object* v_inputString_4943_; uint32_t v_curr_4944_; uint32_t v___x_4945_; uint8_t v___x_4946_; 
v_inputString_4943_ = lean_ctor_get(v_toInputContext_4941_, 0);
v_curr_4944_ = lean_string_utf8_get_fast(v_inputString_4943_, v_pos_4938_);
v___x_4945_ = 58;
v___x_4946_ = lean_uint32_dec_eq(v_curr_4944_, v___x_4945_);
if (v___x_4946_ == 0)
{
return v_s_4936_;
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4947_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_4948_ = lean_box(0);
v___x_4949_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_4936_, v___x_4947_, v___x_4948_, v___x_4946_);
return v___x_4949_;
}
}
else
{
return v_s_4936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_4950_, lean_object* v_s_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_4950_, v_s_4951_);
lean_dec_ref(v_c_4950_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4965_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_4966_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_4967_ = l_Lean_addBuiltinDocString(v___x_4965_, v___x_4966_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_4970_, lean_object* v_p_4971_, lean_object* v_c_4972_, lean_object* v_s_4973_){
_start:
{
lean_object* v___x_4974_; lean_object* v_errorMsg_4975_; 
v___x_4974_ = lean_apply_2(v_p_4971_, v_c_4972_, v_s_4973_);
v_errorMsg_4975_ = lean_ctor_get(v___x_4974_, 4);
lean_inc(v_errorMsg_4975_);
if (lean_obj_tag(v_errorMsg_4975_) == 1)
{
lean_object* v_val_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_5006_; 
v_val_4976_ = lean_ctor_get(v_errorMsg_4975_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v_errorMsg_4975_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4978_ = v_errorMsg_4975_;
v_isShared_4979_ = v_isSharedCheck_5006_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_val_4976_);
lean_dec(v_errorMsg_4975_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_5006_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v_stxStack_4980_; lean_object* v_lhsPrec_4981_; lean_object* v_pos_4982_; lean_object* v_cache_4983_; lean_object* v_recoveredErrors_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_5004_; 
v_stxStack_4980_ = lean_ctor_get(v___x_4974_, 0);
v_lhsPrec_4981_ = lean_ctor_get(v___x_4974_, 1);
v_pos_4982_ = lean_ctor_get(v___x_4974_, 2);
v_cache_4983_ = lean_ctor_get(v___x_4974_, 3);
v_recoveredErrors_4984_ = lean_ctor_get(v___x_4974_, 5);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5004_ == 0)
{
lean_object* v_unused_5005_; 
v_unused_5005_ = lean_ctor_get(v___x_4974_, 4);
lean_dec(v_unused_5005_);
v___x_4986_ = v___x_4974_;
v_isShared_4987_ = v_isSharedCheck_5004_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_recoveredErrors_4984_);
lean_inc(v_cache_4983_);
lean_inc(v_pos_4982_);
lean_inc(v_lhsPrec_4981_);
lean_inc(v_stxStack_4980_);
lean_dec(v___x_4974_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_5004_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v_unexpectedTk_4988_; lean_object* v_unexpected_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5002_; 
v_unexpectedTk_4988_ = lean_ctor_get(v_val_4976_, 0);
v_unexpected_4989_ = lean_ctor_get(v_val_4976_, 1);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_val_4976_);
if (v_isSharedCheck_5002_ == 0)
{
lean_object* v_unused_5003_; 
v_unused_5003_ = lean_ctor_get(v_val_4976_, 2);
lean_dec(v_unused_5003_);
v___x_4991_ = v_val_4976_;
v_isShared_4992_ = v_isSharedCheck_5002_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_unexpected_4989_);
lean_inc(v_unexpectedTk_4988_);
lean_dec(v_val_4976_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5002_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 2, v_expected_4970_);
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_unexpectedTk_4988_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_unexpected_4989_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_expected_4970_);
v___x_4994_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4996_; 
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 0, v___x_4994_);
v___x_4996_ = v___x_4978_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v___x_4994_);
v___x_4996_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
lean_object* v___x_4998_; 
if (v_isShared_4987_ == 0)
{
lean_ctor_set(v___x_4986_, 4, v___x_4996_);
v___x_4998_ = v___x_4986_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_stxStack_4980_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_lhsPrec_4981_);
lean_ctor_set(v_reuseFailAlloc_4999_, 2, v_pos_4982_);
lean_ctor_set(v_reuseFailAlloc_4999_, 3, v_cache_4983_);
lean_ctor_set(v_reuseFailAlloc_4999_, 4, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_4999_, 5, v_recoveredErrors_4984_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_4975_);
lean_dec(v_expected_4970_);
return v___x_4974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5007_, lean_object* v_p_5008_){
_start:
{
lean_object* v_info_5009_; lean_object* v_fn_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5018_; 
v_info_5009_ = lean_ctor_get(v_p_5008_, 0);
v_fn_5010_ = lean_ctor_get(v_p_5008_, 1);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_p_5008_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_5012_ = v_p_5008_;
v_isShared_5013_ = v_isSharedCheck_5018_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_fn_5010_);
lean_inc(v_info_5009_);
lean_dec(v_p_5008_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5018_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5014_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5014_, 0, v_expected_5007_);
lean_closure_set(v___x_5014_, 1, v_fn_5010_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 1, v___x_5014_);
v___x_5016_ = v___x_5012_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_info_5009_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5025_, lean_object* v_s_5026_){
_start:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5027_ = ((lean_object*)(l_Lean_Parser_pushNone___lam__0___closed__1));
v___x_5028_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5026_, v___x_5027_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5029_, lean_object* v_s_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_Parser_pushNone___lam__0(v_x_5029_, v_s_5030_);
lean_dec_ref(v_x_5029_);
return v_res_5031_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5042_ = l_Lean_Parser_symbolNoAntiquot(v___x_5041_);
return v___x_5042_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = lean_unsigned_to_nat(0u);
v___x_5044_ = l_Lean_Parser_termParser(v___x_5043_);
return v___x_5044_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5045_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5046_ = l_Lean_Parser_decQuotDepth(v___x_5045_);
return v___x_5046_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5048_ = l_Lean_Parser_symbolNoAntiquot(v___x_5047_);
return v___x_5048_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5049_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5050_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5051_ = l_Lean_Parser_andthen(v___x_5050_, v___x_5049_);
return v___x_5051_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5053_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5054_ = l_Lean_Parser_andthen(v___x_5053_, v___x_5052_);
return v___x_5054_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5055_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5056_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5057_ = l_Lean_Parser_node(v___x_5056_, v___x_5055_);
return v___x_5057_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5058_; 
v___x_5058_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5058_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5060_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5061_ = l_Lean_Parser_symbolNoAntiquot(v___x_5060_);
return v___x_5061_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5062_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5063_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5064_ = l_Lean_Parser_orelse(v___x_5063_, v___x_5062_);
return v___x_5064_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5065_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5066_ = l_Lean_Parser_identNoAntiquot;
v___x_5067_ = l_Lean_Parser_orelse(v___x_5066_, v___x_5065_);
return v___x_5067_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5068_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5071_ = l_Lean_Parser_checkNoWsBefore(v___x_5070_);
return v___x_5071_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5074_ = l_Lean_Parser_symbolNoAntiquot(v___x_5073_);
return v___x_5074_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5077_ = l_Lean_Parser_symbolNoAntiquot(v___x_5076_);
return v___x_5077_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v___x_5078_ = l_Lean_Parser_antiquotExpr;
v___x_5079_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5080_ = l_Lean_Parser_andthen(v___x_5079_, v___x_5078_);
return v___x_5080_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5081_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5082_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5083_ = l_Lean_Parser_andthen(v___x_5082_, v___x_5081_);
return v___x_5083_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5084_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5085_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5086_ = l_Lean_Parser_andthen(v___x_5085_, v___x_5084_);
return v___x_5086_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5087_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5088_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5089_ = l_Lean_Parser_andthen(v___x_5088_, v___x_5087_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5093_, lean_object* v_s_5094_){
_start:
{
lean_object* v_pos_5095_; lean_object* v_errorMsg_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; 
v_pos_5095_ = lean_ctor_get(v_s_5094_, 2);
v_errorMsg_5096_ = lean_ctor_get(v_s_5094_, 4);
v___x_5097_ = lean_box(0);
lean_inc(v_errorMsg_5096_);
v___x_5098_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5096_, v___x_5097_);
if (v___x_5098_ == 0)
{
lean_dec_ref(v_c_5093_);
return v_s_5094_;
}
else
{
lean_object* v___x_5099_; lean_object* v_fn_5100_; lean_object* v_iniSz_5101_; lean_object* v_s_5102_; lean_object* v_errorMsg_5103_; uint8_t v___x_5104_; 
lean_inc(v_pos_5095_);
v___x_5099_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5100_ = lean_ctor_get(v___x_5099_, 1);
lean_inc_ref(v_fn_5100_);
v_iniSz_5101_ = l_Lean_Parser_ParserState_stackSize(v_s_5094_);
v_s_5102_ = lean_apply_2(v_fn_5100_, v_c_5093_, v_s_5094_);
v_errorMsg_5103_ = lean_ctor_get(v_s_5102_, 4);
lean_inc(v_errorMsg_5103_);
v___x_5104_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5103_, v___x_5097_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; 
v___x_5105_ = l_Lean_Parser_ParserState_restore(v_s_5102_, v_iniSz_5101_, v_pos_5095_);
lean_dec(v_iniSz_5101_);
return v___x_5105_;
}
else
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_dec(v_pos_5095_);
v___x_5106_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5107_ = lean_unsigned_to_nat(1u);
v___x_5108_ = lean_nat_sub(v_iniSz_5101_, v___x_5107_);
lean_dec(v_iniSz_5101_);
v___x_5109_ = l_Lean_Parser_ParserState_mkNode(v_s_5102_, v___x_5106_, v___x_5108_);
lean_dec(v___x_5108_);
return v___x_5109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v_toInputContext_5113_; lean_object* v_s_5114_; lean_object* v_pos_5115_; lean_object* v_inputString_5116_; uint32_t v___x_5117_; uint32_t v___x_5118_; uint8_t v___x_5119_; 
v_toInputContext_5113_ = lean_ctor_get(v___y_5111_, 0);
lean_inc_ref(v___y_5111_);
v_s_5114_ = lean_apply_2(v_fn_5110_, v___y_5111_, v___y_5112_);
v_pos_5115_ = lean_ctor_get(v_s_5114_, 2);
lean_inc(v_pos_5115_);
v_inputString_5116_ = lean_ctor_get(v_toInputContext_5113_, 0);
v___x_5117_ = lean_string_utf8_get(v_inputString_5116_, v_pos_5115_);
lean_dec(v_pos_5115_);
v___x_5118_ = 37;
v___x_5119_ = lean_uint32_dec_eq(v___x_5117_, v___x_5118_);
if (v___x_5119_ == 0)
{
lean_dec_ref(v___y_5111_);
return v_s_5114_;
}
else
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Parser_tokenAntiquotFn(v___y_5111_, v_s_5114_);
return v___x_5120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5121_){
_start:
{
lean_object* v_info_5122_; lean_object* v_fn_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5131_; 
v_info_5122_ = lean_ctor_get(v_p_5121_, 0);
v_fn_5123_ = lean_ctor_get(v_p_5121_, 1);
v_isSharedCheck_5131_ = !lean_is_exclusive(v_p_5121_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5125_ = v_p_5121_;
v_isShared_5126_ = v_isSharedCheck_5131_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_fn_5123_);
lean_inc(v_info_5122_);
lean_dec(v_p_5121_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5131_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___f_5127_; lean_object* v___x_5129_; 
v___f_5127_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5127_, 0, v_fn_5123_);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 1, v___f_5127_);
v___x_5129_ = v___x_5125_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_info_5122_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___f_5127_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5132_){
_start:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5133_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5132_);
v___x_5134_ = l_Lean_Parser_tokenWithAntiquot(v___x_5133_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5137_, uint8_t v_includeIdent_5138_){
_start:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5139_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5137_, v_includeIdent_5138_);
v___x_5140_ = l_Lean_Parser_tokenWithAntiquot(v___x_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5141_, lean_object* v_includeIdent_5142_){
_start:
{
uint8_t v_includeIdent_boxed_5143_; lean_object* v_res_5144_; 
v_includeIdent_boxed_5143_ = lean_unbox(v_includeIdent_5142_);
v_res_5144_ = l_Lean_Parser_nonReservedSymbol(v_sym_5141_, v_includeIdent_boxed_5143_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5145_, lean_object* v_asciiSym_5146_){
_start:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5147_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5145_, v_asciiSym_5146_);
v___x_5148_ = l_Lean_Parser_tokenWithAntiquot(v___x_5147_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5149_, lean_object* v_asciiSym_5150_, uint8_t v_preserveForPP_5151_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5149_, v_asciiSym_5150_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5153_, lean_object* v_asciiSym_5154_, lean_object* v_preserveForPP_5155_){
_start:
{
uint8_t v_preserveForPP_boxed_5156_; lean_object* v_res_5157_; 
v_preserveForPP_boxed_5156_ = lean_unbox(v_preserveForPP_5155_);
v_res_5157_ = l_Lean_Parser_unicodeSymbol(v_sym_5153_, v_asciiSym_5154_, v_preserveForPP_boxed_5156_);
return v_res_5157_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5158_; lean_object* v___x_5159_; 
v___x_5158_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5159_ = l_Lean_Parser_symbol(v___x_5158_);
return v___x_5159_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5160_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5161_ = lean_box(0);
v___x_5162_ = l_Lean_Parser_setExpected(v___x_5161_, v___x_5160_);
return v___x_5162_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5163_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5164_ = l_Lean_Parser_checkNoWsBefore(v___x_5163_);
return v___x_5164_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
v___x_5165_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5166_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5167_ = l_Lean_Parser_andthen(v___x_5166_, v___x_5165_);
return v___x_5167_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5168_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5169_ = l_Lean_Parser_manyNoAntiquot(v___x_5168_);
return v___x_5169_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5171_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5172_ = l_Lean_Parser_checkNoWsBefore(v___x_5171_);
return v___x_5172_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5181_; lean_object* v___x_5182_; 
v___x_5181_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5182_ = l_Lean_Parser_symbol(v___x_5181_);
return v___x_5182_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5183_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5184_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5185_ = l_Lean_Parser_andthen(v___x_5184_, v___x_5183_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5189_, lean_object* v_kind_5190_, uint8_t v_anonymous_5191_, uint8_t v_isPseudoKind_5192_){
_start:
{
lean_object* v___y_5194_; lean_object* v___y_5195_; lean_object* v___y_5208_; 
if (v_isPseudoKind_5192_ == 0)
{
lean_object* v___x_5226_; 
v___x_5226_ = lean_box(0);
v___y_5208_ = v___x_5226_;
goto v___jp_5207_;
}
else
{
lean_object* v___x_5227_; 
v___x_5227_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5208_ = v___x_5227_;
goto v___jp_5207_;
}
v___jp_5193_:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5196_ = l_Lean_Parser_maxPrec;
v___x_5197_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5198_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5199_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5200_ = l_Lean_Parser_antiquotExpr;
v___x_5201_ = l_Lean_Parser_andthen(v___x_5200_, v___y_5195_);
v___x_5202_ = l_Lean_Parser_andthen(v___x_5199_, v___x_5201_);
v___x_5203_ = l_Lean_Parser_andthen(v___x_5198_, v___x_5202_);
v___x_5204_ = l_Lean_Parser_andthen(v___x_5197_, v___x_5203_);
v___x_5205_ = l_Lean_Parser_atomic(v___x_5204_);
v___x_5206_ = l_Lean_Parser_leadingNode(v___y_5194_, v___x_5196_, v___x_5205_);
return v___x_5206_;
}
v___jp_5207_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v_kind_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; uint8_t v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v_nameP_5223_; 
v___x_5209_ = l_Lean_Name_append(v_kind_5190_, v___y_5208_);
v___x_5210_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5211_ = l_Lean_Name_append(v___x_5209_, v___x_5210_);
v___x_5212_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5213_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5214_ = lean_string_append(v___x_5213_, v_name_5189_);
v___x_5215_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5216_ = lean_string_append(v___x_5214_, v___x_5215_);
v___x_5217_ = l_Lean_Parser_checkNoWsBefore(v___x_5216_);
v___x_5218_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5219_ = 0;
v___x_5220_ = l_Lean_Parser_nonReservedSymbol(v_name_5189_, v___x_5219_);
v___x_5221_ = l_Lean_Parser_andthen(v___x_5218_, v___x_5220_);
v___x_5222_ = l_Lean_Parser_andthen(v___x_5217_, v___x_5221_);
v_nameP_5223_ = l_Lean_Parser_node(v___x_5212_, v___x_5222_);
if (v_anonymous_5191_ == 0)
{
v___y_5194_ = v_kind_5211_;
v___y_5195_ = v_nameP_5223_;
goto v___jp_5193_;
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5224_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5225_ = l_Lean_Parser_orelse(v_nameP_5223_, v___x_5224_);
v___y_5194_ = v_kind_5211_;
v___y_5195_ = v___x_5225_;
goto v___jp_5193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5228_, lean_object* v_kind_5229_, lean_object* v_anonymous_5230_, lean_object* v_isPseudoKind_5231_){
_start:
{
uint8_t v_anonymous_boxed_5232_; uint8_t v_isPseudoKind_boxed_5233_; lean_object* v_res_5234_; 
v_anonymous_boxed_5232_ = lean_unbox(v_anonymous_5230_);
v_isPseudoKind_boxed_5233_ = lean_unbox(v_isPseudoKind_5231_);
v_res_5234_ = l_Lean_Parser_mkAntiquot(v_name_5228_, v_kind_5229_, v_anonymous_boxed_5232_, v_isPseudoKind_boxed_5233_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5242_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5243_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5244_ = l_Lean_addBuiltinDocString(v___x_5242_, v___x_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5247_, lean_object* v_p_5248_, uint8_t v_isCatAntiquot_5249_, lean_object* v_c_5250_, lean_object* v_s_5251_){
_start:
{
lean_object* v_toInputContext_5252_; lean_object* v_pos_5253_; lean_object* v_inputString_5254_; uint32_t v___x_5255_; uint32_t v___x_5256_; uint8_t v___x_5257_; 
v_toInputContext_5252_ = lean_ctor_get(v_c_5250_, 0);
v_pos_5253_ = lean_ctor_get(v_s_5251_, 2);
v_inputString_5254_ = lean_ctor_get(v_toInputContext_5252_, 0);
v___x_5255_ = lean_string_utf8_get(v_inputString_5254_, v_pos_5253_);
v___x_5256_ = 36;
v___x_5257_ = lean_uint32_dec_eq(v___x_5255_, v___x_5256_);
if (v___x_5257_ == 0)
{
lean_object* v___x_5258_; 
lean_dec_ref(v_antiquotP_5247_);
v___x_5258_ = lean_apply_2(v_p_5248_, v_c_5250_, v_s_5251_);
return v___x_5258_;
}
else
{
if (v_isCatAntiquot_5249_ == 0)
{
uint8_t v___x_5259_; lean_object* v___x_5260_; 
v___x_5259_ = 1;
v___x_5260_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5247_, v_p_5248_, v___x_5259_, v_c_5250_, v_s_5251_);
return v___x_5260_;
}
else
{
uint8_t v___x_5261_; lean_object* v___x_5262_; 
v___x_5261_ = 0;
v___x_5262_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5247_, v_p_5248_, v___x_5261_, v_c_5250_, v_s_5251_);
return v___x_5262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5263_, lean_object* v_p_5264_, lean_object* v_isCatAntiquot_5265_, lean_object* v_c_5266_, lean_object* v_s_5267_){
_start:
{
uint8_t v_isCatAntiquot_boxed_5268_; lean_object* v_res_5269_; 
v_isCatAntiquot_boxed_5268_ = lean_unbox(v_isCatAntiquot_5265_);
v_res_5269_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5263_, v_p_5264_, v_isCatAntiquot_boxed_5268_, v_c_5266_, v_s_5267_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5270_, lean_object* v_p_5271_){
_start:
{
lean_object* v_info_5272_; lean_object* v_fn_5273_; lean_object* v_info_5274_; lean_object* v_fn_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5286_; 
v_info_5272_ = lean_ctor_get(v_antiquotP_5270_, 0);
lean_inc_ref(v_info_5272_);
v_fn_5273_ = lean_ctor_get(v_antiquotP_5270_, 1);
lean_inc_ref(v_fn_5273_);
lean_dec_ref(v_antiquotP_5270_);
v_info_5274_ = lean_ctor_get(v_p_5271_, 0);
v_fn_5275_ = lean_ctor_get(v_p_5271_, 1);
v_isSharedCheck_5286_ = !lean_is_exclusive(v_p_5271_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5277_ = v_p_5271_;
v_isShared_5278_ = v_isSharedCheck_5286_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_fn_5275_);
lean_inc(v_info_5274_);
lean_dec(v_p_5271_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5286_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5279_; uint8_t v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5284_; 
v___x_5279_ = l_Lean_Parser_orelseInfo(v_info_5272_, v_info_5274_);
v___x_5280_ = 0;
v___x_5281_ = lean_box(v___x_5280_);
v___x_5282_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5282_, 0, v_fn_5273_);
lean_closure_set(v___x_5282_, 1, v_fn_5275_);
lean_closure_set(v___x_5282_, 2, v___x_5281_);
if (v_isShared_5278_ == 0)
{
lean_ctor_set(v___x_5277_, 1, v___x_5282_);
lean_ctor_set(v___x_5277_, 0, v___x_5279_);
v___x_5284_ = v___x_5277_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5279_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v___x_5282_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5294_ = ((lean_object*)(l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5295_ = ((lean_object*)(l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5296_ = l_Lean_addBuiltinDocString(v___x_5294_, v___x_5295_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5299_){
_start:
{
lean_object* v_fn_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5308_; 
v_fn_5300_ = lean_ctor_get(v_p_5299_, 1);
v_isSharedCheck_5308_ = !lean_is_exclusive(v_p_5299_);
if (v_isSharedCheck_5308_ == 0)
{
lean_object* v_unused_5309_; 
v_unused_5309_ = lean_ctor_get(v_p_5299_, 0);
lean_dec(v_unused_5309_);
v___x_5302_ = v_p_5299_;
v_isShared_5303_ = v_isSharedCheck_5308_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_fn_5300_);
lean_dec(v_p_5299_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5308_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5304_; lean_object* v___x_5306_; 
v___x_5304_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 0, v___x_5304_);
v___x_5306_ = v___x_5302_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5307_, 1, v_fn_5300_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5313_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5314_ = l_Lean_Parser_symbol(v___x_5313_);
return v___x_5314_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5315_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5316_ = l_Lean_Parser_symbol(v___x_5315_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5317_, lean_object* v_p_5318_, lean_object* v_suffix_5319_){
_start:
{
lean_object* v___x_5320_; lean_object* v_kind_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; 
v___x_5320_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5321_ = l_Lean_Name_append(v_kind_5317_, v___x_5320_);
v___x_5322_ = l_Lean_Parser_maxPrec;
v___x_5323_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5324_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5325_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5326_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5327_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5328_ = l_Lean_Parser_node(v___x_5327_, v_p_5318_);
v___x_5329_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5330_ = l_Lean_Parser_andthen(v___x_5329_, v_suffix_5319_);
v___x_5331_ = l_Lean_Parser_andthen(v___x_5328_, v___x_5330_);
v___x_5332_ = l_Lean_Parser_andthen(v___x_5326_, v___x_5331_);
v___x_5333_ = l_Lean_Parser_andthen(v___x_5325_, v___x_5332_);
v___x_5334_ = l_Lean_Parser_andthen(v___x_5324_, v___x_5333_);
v___x_5335_ = l_Lean_Parser_andthen(v___x_5323_, v___x_5334_);
v___x_5336_ = l_Lean_Parser_atomic(v___x_5335_);
v___x_5337_ = l_Lean_Parser_leadingNode(v_kind_5321_, v___x_5322_, v___x_5336_);
return v___x_5337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5345_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5346_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5347_ = l_Lean_addBuiltinDocString(v___x_5345_, v___x_5346_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5353_, lean_object* v_suffix_5354_, lean_object* v_c_5355_, lean_object* v_s_5356_){
_start:
{
lean_object* v_pos_5357_; lean_object* v_iniSz_5358_; lean_object* v_s_5359_; lean_object* v_stxStack_5360_; lean_object* v_errorMsg_5361_; lean_object* v___x_5362_; uint8_t v___x_5363_; 
v_pos_5357_ = lean_ctor_get(v_s_5356_, 2);
lean_inc(v_pos_5357_);
v_iniSz_5358_ = l_Lean_Parser_ParserState_stackSize(v_s_5356_);
v_s_5359_ = lean_apply_2(v_suffix_5354_, v_c_5355_, v_s_5356_);
v_stxStack_5360_ = lean_ctor_get(v_s_5359_, 0);
lean_inc_ref(v_stxStack_5360_);
v_errorMsg_5361_ = lean_ctor_get(v_s_5359_, 4);
lean_inc(v_errorMsg_5361_);
v___x_5362_ = lean_box(0);
v___x_5363_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5361_, v___x_5362_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; 
lean_dec_ref(v_stxStack_5360_);
lean_dec(v_kind_5353_);
v___x_5364_ = l_Lean_Parser_ParserState_restore(v_s_5359_, v_iniSz_5358_, v_pos_5357_);
lean_dec(v_iniSz_5358_);
return v___x_5364_;
}
else
{
lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; 
lean_dec(v_iniSz_5358_);
lean_dec(v_pos_5357_);
v___x_5365_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5366_ = l_Lean_Name_append(v_kind_5353_, v___x_5365_);
v___x_5367_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5360_);
lean_dec_ref(v_stxStack_5360_);
v___x_5368_ = lean_unsigned_to_nat(2u);
v___x_5369_ = lean_nat_sub(v___x_5367_, v___x_5368_);
lean_dec(v___x_5367_);
v___x_5370_ = l_Lean_Parser_ParserState_mkNode(v_s_5359_, v___x_5366_, v___x_5369_);
lean_dec(v___x_5369_);
return v___x_5370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5371_, lean_object* v_kind_5372_, lean_object* v_fn_5373_, lean_object* v_c_5374_, lean_object* v_s_5375_){
_start:
{
lean_object* v_s_5376_; lean_object* v_stxStack_5377_; lean_object* v_errorMsg_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
lean_inc_ref(v_c_5374_);
v_s_5376_ = lean_apply_2(v_fn_5371_, v_c_5374_, v_s_5375_);
v_stxStack_5377_ = lean_ctor_get(v_s_5376_, 0);
lean_inc_ref(v_stxStack_5377_);
v_errorMsg_5378_ = lean_ctor_get(v_s_5376_, 4);
lean_inc(v_errorMsg_5378_);
v___x_5379_ = lean_box(0);
v___x_5380_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5378_, v___x_5379_);
if (v___x_5380_ == 0)
{
lean_dec_ref(v_stxStack_5377_);
lean_dec_ref(v_c_5374_);
lean_dec_ref(v_fn_5373_);
lean_dec(v_kind_5372_);
return v_s_5376_;
}
else
{
lean_object* v___x_5381_; uint8_t v___x_5382_; 
v___x_5381_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5377_);
lean_dec_ref(v_stxStack_5377_);
v___x_5382_ = l_Lean_Syntax_isAntiquots(v___x_5381_);
if (v___x_5382_ == 0)
{
lean_dec_ref(v_c_5374_);
lean_dec_ref(v_fn_5373_);
lean_dec(v_kind_5372_);
return v_s_5376_;
}
else
{
lean_object* v___x_5383_; 
v___x_5383_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5372_, v_fn_5373_, v_c_5374_, v_s_5376_);
return v___x_5383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5384_, lean_object* v_p_5385_, lean_object* v_suffix_5386_){
_start:
{
lean_object* v_info_5387_; lean_object* v_fn_5388_; lean_object* v_info_5389_; lean_object* v_fn_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5399_; 
v_info_5387_ = lean_ctor_get(v_p_5385_, 0);
lean_inc_ref(v_info_5387_);
v_fn_5388_ = lean_ctor_get(v_p_5385_, 1);
lean_inc_ref(v_fn_5388_);
lean_dec_ref(v_p_5385_);
v_info_5389_ = lean_ctor_get(v_suffix_5386_, 0);
v_fn_5390_ = lean_ctor_get(v_suffix_5386_, 1);
v_isSharedCheck_5399_ = !lean_is_exclusive(v_suffix_5386_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5392_ = v_suffix_5386_;
v_isShared_5393_ = v_isSharedCheck_5399_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_fn_5390_);
lean_inc(v_info_5389_);
lean_dec(v_suffix_5386_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5399_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___f_5394_; lean_object* v___x_5395_; lean_object* v___x_5397_; 
v___f_5394_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5394_, 0, v_fn_5388_);
lean_closure_set(v___f_5394_, 1, v_kind_5384_);
lean_closure_set(v___f_5394_, 2, v_fn_5390_);
v___x_5395_ = l_Lean_Parser_andthenInfo(v_info_5387_, v_info_5389_);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 1, v___f_5394_);
lean_ctor_set(v___x_5392_, 0, v___x_5395_);
v___x_5397_ = v___x_5392_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5395_);
lean_ctor_set(v_reuseFailAlloc_5398_, 1, v___f_5394_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5407_ = ((lean_object*)(l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5408_ = ((lean_object*)(l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5409_ = l_Lean_addBuiltinDocString(v___x_5407_, v___x_5408_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5412_, lean_object* v_p_5413_, lean_object* v_suffix_5414_){
_start:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
lean_inc_ref(v_p_5413_);
v___x_5415_ = l_Lean_Parser_withoutInfo(v_p_5413_);
lean_inc_ref(v_suffix_5414_);
lean_inc(v_kind_5412_);
v___x_5416_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5412_, v___x_5415_, v_suffix_5414_);
v___x_5417_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5412_, v_p_5413_, v_suffix_5414_);
v___x_5418_ = l_Lean_Parser_withAntiquot(v___x_5416_, v___x_5417_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5419_, lean_object* v_kind_5420_, lean_object* v_p_5421_, uint8_t v_anonymous_5422_){
_start:
{
uint8_t v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5423_ = 0;
lean_inc(v_kind_5420_);
v___x_5424_ = l_Lean_Parser_mkAntiquot(v_name_5419_, v_kind_5420_, v_anonymous_5422_, v___x_5423_);
v___x_5425_ = l_Lean_Parser_node(v_kind_5420_, v_p_5421_);
v___x_5426_ = l_Lean_Parser_withAntiquot(v___x_5424_, v___x_5425_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5427_, lean_object* v_kind_5428_, lean_object* v_p_5429_, lean_object* v_anonymous_5430_){
_start:
{
uint8_t v_anonymous_boxed_5431_; lean_object* v_res_5432_; 
v_anonymous_boxed_5431_ = lean_unbox(v_anonymous_5430_);
v_res_5432_ = l_Lean_Parser_nodeWithAntiquot(v_name_5427_, v_kind_5428_, v_p_5429_, v_anonymous_boxed_5431_);
return v_res_5432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5437_, lean_object* v_sep_5438_){
_start:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v_str_5443_; lean_object* v_startInclusive_5444_; lean_object* v_endExclusive_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
v___x_5439_ = lean_unsigned_to_nat(0u);
v___x_5440_ = lean_string_utf8_byte_size(v_sep_5438_);
v___x_5441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5441_, 0, v_sep_5438_);
lean_ctor_set(v___x_5441_, 1, v___x_5439_);
lean_ctor_set(v___x_5441_, 2, v___x_5440_);
v___x_5442_ = l_String_Slice_trimAscii(v___x_5441_);
v_str_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc_ref(v_str_5443_);
v_startInclusive_5444_ = lean_ctor_get(v___x_5442_, 1);
lean_inc(v_startInclusive_5444_);
v_endExclusive_5445_ = lean_ctor_get(v___x_5442_, 2);
lean_inc(v_endExclusive_5445_);
lean_dec_ref(v___x_5442_);
v___x_5446_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5447_ = lean_string_utf8_extract(v_str_5443_, v_startInclusive_5444_, v_endExclusive_5445_);
lean_dec(v_endExclusive_5445_);
lean_dec(v_startInclusive_5444_);
lean_dec_ref(v_str_5443_);
v___x_5448_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5449_ = lean_string_append(v___x_5447_, v___x_5448_);
v___x_5450_ = l_Lean_Parser_symbol(v___x_5449_);
v___x_5451_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5446_, v_p_5437_, v___x_5450_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5452_, lean_object* v_sep_5453_, lean_object* v_psep_5454_, uint8_t v_allowTrailingSep_5455_){
_start:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5456_ = l_Lean_Parser_sepByElemParser(v_p_5452_, v_sep_5453_);
v___x_5457_ = l_Lean_Parser_sepByNoAntiquot(v___x_5456_, v_psep_5454_, v_allowTrailingSep_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5458_, lean_object* v_sep_5459_, lean_object* v_psep_5460_, lean_object* v_allowTrailingSep_5461_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5462_; lean_object* v_res_5463_; 
v_allowTrailingSep_boxed_5462_ = lean_unbox(v_allowTrailingSep_5461_);
v_res_5463_ = l_Lean_Parser_sepBy(v_p_5458_, v_sep_5459_, v_psep_5460_, v_allowTrailingSep_boxed_5462_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5464_, lean_object* v_sep_5465_, lean_object* v_psep_5466_, uint8_t v_allowTrailingSep_5467_){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = l_Lean_Parser_sepByElemParser(v_p_5464_, v_sep_5465_);
v___x_5469_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5468_, v_psep_5466_, v_allowTrailingSep_5467_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5470_, lean_object* v_sep_5471_, lean_object* v_psep_5472_, lean_object* v_allowTrailingSep_5473_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5474_; lean_object* v_res_5475_; 
v_allowTrailingSep_boxed_5474_ = lean_unbox(v_allowTrailingSep_5473_);
v_res_5475_ = l_Lean_Parser_sepBy1(v_p_5470_, v_sep_5471_, v_psep_5472_, v_allowTrailingSep_boxed_5474_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5476_, lean_object* v_iniSz_5477_){
_start:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; uint8_t v___x_5481_; 
v___x_5478_ = l_Lean_Parser_ParserState_stackSize(v_s_5476_);
v___x_5479_ = lean_unsigned_to_nat(1u);
v___x_5480_ = lean_nat_add(v_iniSz_5477_, v___x_5479_);
v___x_5481_ = lean_nat_dec_eq(v___x_5478_, v___x_5480_);
lean_dec(v___x_5480_);
lean_dec(v___x_5478_);
if (v___x_5481_ == 0)
{
lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5482_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5483_ = l_Lean_Parser_ParserState_mkNode(v_s_5476_, v___x_5482_, v_iniSz_5477_);
return v___x_5483_;
}
else
{
return v_s_5476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5484_, lean_object* v_iniSz_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5484_, v_iniSz_5485_);
lean_dec(v_iniSz_5485_);
return v_res_5486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5487_, lean_object* v_tables_5488_, uint8_t v_behavior_5489_, lean_object* v_c_5490_, lean_object* v_s_5491_){
_start:
{
lean_object* v_leadingTable_5492_; lean_object* v_leadingParsers_5493_; lean_object* v_iniSz_5494_; lean_object* v___x_5495_; lean_object* v_fst_5496_; lean_object* v_snd_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5519_; 
v_leadingTable_5492_ = lean_ctor_get(v_tables_5488_, 0);
lean_inc(v_leadingTable_5492_);
v_leadingParsers_5493_ = lean_ctor_get(v_tables_5488_, 1);
lean_inc(v_leadingParsers_5493_);
lean_dec_ref(v_tables_5488_);
v_iniSz_5494_ = l_Lean_Parser_ParserState_stackSize(v_s_5491_);
lean_inc_ref(v_c_5490_);
v___x_5495_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5492_, v_c_5490_, v_s_5491_, v_behavior_5489_);
lean_dec(v_leadingTable_5492_);
v_fst_5496_ = lean_ctor_get(v___x_5495_, 0);
v_snd_5497_ = lean_ctor_get(v___x_5495_, 1);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5499_ = v___x_5495_;
v_isShared_5500_ = v_isSharedCheck_5519_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_snd_5497_);
lean_inc(v_fst_5496_);
lean_dec(v___x_5495_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5519_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v_errorMsg_5501_; lean_object* v___x_5502_; uint8_t v___x_5503_; 
v_errorMsg_5501_ = lean_ctor_get(v_fst_5496_, 4);
v___x_5502_ = lean_box(0);
lean_inc(v_errorMsg_5501_);
v___x_5503_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5501_, v___x_5502_);
if (v___x_5503_ == 0)
{
lean_del_object(v___x_5499_);
lean_dec(v_snd_5497_);
lean_dec(v_iniSz_5494_);
lean_dec(v_leadingParsers_5493_);
lean_dec_ref(v_c_5490_);
lean_dec(v_kind_5487_);
return v_fst_5496_;
}
else
{
lean_object* v_ps_5504_; uint8_t v___x_5505_; 
v_ps_5504_ = l_List_appendTR___redArg(v_leadingParsers_5493_, v_snd_5497_);
v___x_5505_ = l_List_isEmpty___redArg(v_ps_5504_);
if (v___x_5505_ == 0)
{
lean_object* v_s_5506_; lean_object* v___x_5507_; 
lean_del_object(v___x_5499_);
lean_dec(v_kind_5487_);
v_s_5506_ = l_Lean_Parser_longestMatchFn(v___x_5502_, v_ps_5504_, v_c_5490_, v_fst_5496_);
v___x_5507_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5506_, v_iniSz_5494_);
lean_dec(v_iniSz_5494_);
return v___x_5507_;
}
else
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5511_; 
lean_dec(v_ps_5504_);
lean_dec(v_iniSz_5494_);
v___x_5508_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5487_, v___x_5505_);
v___x_5509_ = lean_box(0);
lean_inc_ref(v___x_5508_);
if (v_isShared_5500_ == 0)
{
lean_ctor_set_tag(v___x_5499_, 1);
lean_ctor_set(v___x_5499_, 1, v___x_5509_);
lean_ctor_set(v___x_5499_, 0, v___x_5508_);
v___x_5511_ = v___x_5499_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5509_);
v___x_5511_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
lean_object* v_s_5512_; lean_object* v_errorMsg_5516_; uint8_t v___x_5517_; 
v_s_5512_ = l_Lean_Parser_tokenFn(v___x_5511_, v_c_5490_, v_fst_5496_);
v_errorMsg_5516_ = lean_ctor_get(v_s_5512_, 4);
lean_inc(v_errorMsg_5516_);
v___x_5517_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5516_, v___x_5502_);
if (v___x_5517_ == 0)
{
if (v___x_5505_ == 0)
{
goto v___jp_5513_;
}
else
{
lean_dec_ref(v___x_5508_);
return v_s_5512_;
}
}
else
{
goto v___jp_5513_;
}
v___jp_5513_:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = lean_unsigned_to_nat(0u);
v___x_5515_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5512_, v___x_5508_, v___x_5514_);
return v___x_5515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5520_, lean_object* v_tables_5521_, lean_object* v_behavior_5522_, lean_object* v_c_5523_, lean_object* v_s_5524_){
_start:
{
uint8_t v_behavior_boxed_5525_; lean_object* v_res_5526_; 
v_behavior_boxed_5525_ = lean_unbox(v_behavior_5522_);
v_res_5526_ = l_Lean_Parser_leadingParserAux(v_kind_5520_, v_tables_5521_, v_behavior_boxed_5525_, v_c_5523_, v_s_5524_);
return v_res_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5527_, lean_object* v_tables_5528_, uint8_t v_behavior_5529_, lean_object* v_antiquotParser_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_){
_start:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; uint8_t v___x_5535_; lean_object* v___x_5536_; 
v___x_5533_ = lean_box(v_behavior_5529_);
v___x_5534_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5534_, 0, v_kind_5527_);
lean_closure_set(v___x_5534_, 1, v_tables_5528_);
lean_closure_set(v___x_5534_, 2, v___x_5533_);
v___x_5535_ = 1;
v___x_5536_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5530_, v___x_5534_, v___x_5535_, v_a_5531_, v_a_5532_);
return v___x_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5537_, lean_object* v_tables_5538_, lean_object* v_behavior_5539_, lean_object* v_antiquotParser_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_){
_start:
{
uint8_t v_behavior_boxed_5543_; lean_object* v_res_5544_; 
v_behavior_boxed_5543_ = lean_unbox(v_behavior_5539_);
v_res_5544_ = l_Lean_Parser_leadingParser(v_kind_5537_, v_tables_5538_, v_behavior_boxed_5543_, v_antiquotParser_5540_, v_a_5541_, v_a_5542_);
return v_res_5544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5545_, lean_object* v_left_5546_, lean_object* v_ps_5547_, lean_object* v_c_5548_, lean_object* v_s_5549_){
_start:
{
lean_object* v_trailingParsers_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
v_trailingParsers_5550_ = lean_ctor_get(v_tables_5545_, 3);
lean_inc(v_trailingParsers_5550_);
lean_dec_ref(v_tables_5545_);
v___x_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5551_, 0, v_left_5546_);
v___x_5552_ = l_List_appendTR___redArg(v_ps_5547_, v_trailingParsers_5550_);
v___x_5553_ = l_Lean_Parser_longestMatchFn(v___x_5551_, v___x_5552_, v_c_5548_, v_s_5549_);
return v___x_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5554_, lean_object* v_c_5555_, lean_object* v_s_5556_){
_start:
{
lean_object* v_pos_5557_; lean_object* v_trailingTable_5558_; lean_object* v_trailingParsers_5559_; lean_object* v_iniSz_5560_; uint8_t v___x_5561_; lean_object* v___x_5562_; lean_object* v_fst_5563_; lean_object* v_snd_5564_; lean_object* v_stxStack_5565_; lean_object* v_errorMsg_5566_; uint8_t v___y_5568_; lean_object* v___x_5582_; uint8_t v___x_5583_; 
v_pos_5557_ = lean_ctor_get(v_s_5556_, 2);
lean_inc(v_pos_5557_);
v_trailingTable_5558_ = lean_ctor_get(v_tables_5554_, 2);
v_trailingParsers_5559_ = lean_ctor_get(v_tables_5554_, 3);
v_iniSz_5560_ = l_Lean_Parser_ParserState_stackSize(v_s_5556_);
v___x_5561_ = 0;
lean_inc_ref(v_c_5555_);
v___x_5562_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5558_, v_c_5555_, v_s_5556_, v___x_5561_);
v_fst_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_fst_5563_);
v_snd_5564_ = lean_ctor_get(v___x_5562_, 1);
lean_inc(v_snd_5564_);
lean_dec_ref(v___x_5562_);
v_stxStack_5565_ = lean_ctor_get(v_fst_5563_, 0);
v_errorMsg_5566_ = lean_ctor_get(v_fst_5563_, 4);
v___x_5582_ = lean_box(0);
lean_inc(v_errorMsg_5566_);
v___x_5583_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5566_, v___x_5582_);
if (v___x_5583_ == 0)
{
lean_object* v___x_5584_; 
lean_dec(v_snd_5564_);
lean_dec_ref(v_c_5555_);
lean_dec_ref(v_tables_5554_);
v___x_5584_ = l_Lean_Parser_ParserState_restore(v_fst_5563_, v_iniSz_5560_, v_pos_5557_);
lean_dec(v_iniSz_5560_);
return v___x_5584_;
}
else
{
uint8_t v___x_5585_; 
v___x_5585_ = l_List_isEmpty___redArg(v_snd_5564_);
if (v___x_5585_ == 0)
{
v___y_5568_ = v___x_5585_;
goto v___jp_5567_;
}
else
{
uint8_t v___x_5586_; 
v___x_5586_ = l_List_isEmpty___redArg(v_trailingParsers_5559_);
v___y_5568_ = v___x_5586_;
goto v___jp_5567_;
}
}
v___jp_5567_:
{
if (v___y_5568_ == 0)
{
lean_object* v_left_5569_; lean_object* v_s_5570_; lean_object* v_s_5571_; lean_object* v_pos_5572_; lean_object* v_errorMsg_5573_; lean_object* v___x_5574_; uint8_t v___x_5575_; 
v_left_5569_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5565_);
v_s_5570_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5563_);
lean_inc_ref(v_c_5555_);
lean_inc(v_left_5569_);
lean_inc_ref(v_tables_5554_);
v_s_5571_ = l_Lean_Parser_trailingLoopStep(v_tables_5554_, v_left_5569_, v_snd_5564_, v_c_5555_, v_s_5570_);
v_pos_5572_ = lean_ctor_get(v_s_5571_, 2);
lean_inc(v_pos_5572_);
v_errorMsg_5573_ = lean_ctor_get(v_s_5571_, 4);
lean_inc(v_errorMsg_5573_);
v___x_5574_ = lean_box(0);
v___x_5575_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5573_, v___x_5574_);
if (v___x_5575_ == 0)
{
uint8_t v___x_5576_; 
lean_dec_ref(v_c_5555_);
lean_dec_ref(v_tables_5554_);
v___x_5576_ = lean_nat_dec_eq(v_pos_5572_, v_pos_5557_);
lean_dec(v_pos_5572_);
if (v___x_5576_ == 0)
{
lean_dec(v_left_5569_);
lean_dec(v_iniSz_5560_);
lean_dec(v_pos_5557_);
return v_s_5571_;
}
else
{
lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; 
v___x_5577_ = lean_unsigned_to_nat(1u);
v___x_5578_ = lean_nat_sub(v_iniSz_5560_, v___x_5577_);
lean_dec(v_iniSz_5560_);
v___x_5579_ = l_Lean_Parser_ParserState_restore(v_s_5571_, v___x_5578_, v_pos_5557_);
lean_dec(v___x_5578_);
v___x_5580_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5579_, v_left_5569_);
return v___x_5580_;
}
}
else
{
lean_dec(v_pos_5572_);
lean_dec(v_left_5569_);
lean_dec(v_iniSz_5560_);
lean_dec(v_pos_5557_);
v_s_5556_ = v_s_5571_;
goto _start;
}
}
else
{
lean_dec(v_snd_5564_);
lean_dec(v_iniSz_5560_);
lean_dec(v_pos_5557_);
lean_dec_ref(v_c_5555_);
lean_dec_ref(v_tables_5554_);
return v_fst_5563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5587_, lean_object* v_tables_5588_, uint8_t v_behavior_5589_, lean_object* v_antiquotParser_5590_, lean_object* v_c_5591_, lean_object* v_s_5592_){
_start:
{
lean_object* v_s_5593_; lean_object* v_errorMsg_5594_; lean_object* v___x_5595_; uint8_t v___x_5596_; 
lean_inc_ref(v_c_5591_);
lean_inc_ref(v_tables_5588_);
v_s_5593_ = l_Lean_Parser_leadingParser(v_kind_5587_, v_tables_5588_, v_behavior_5589_, v_antiquotParser_5590_, v_c_5591_, v_s_5592_);
v_errorMsg_5594_ = lean_ctor_get(v_s_5593_, 4);
lean_inc(v_errorMsg_5594_);
v___x_5595_ = lean_box(0);
v___x_5596_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5594_, v___x_5595_);
if (v___x_5596_ == 0)
{
lean_dec_ref(v_c_5591_);
lean_dec_ref(v_tables_5588_);
return v_s_5593_;
}
else
{
lean_object* v___x_5597_; 
v___x_5597_ = l_Lean_Parser_trailingLoop(v_tables_5588_, v_c_5591_, v_s_5593_);
return v___x_5597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5598_, lean_object* v_tables_5599_, lean_object* v_behavior_5600_, lean_object* v_antiquotParser_5601_, lean_object* v_c_5602_, lean_object* v_s_5603_){
_start:
{
uint8_t v_behavior_boxed_5604_; lean_object* v_res_5605_; 
v_behavior_boxed_5604_ = lean_unbox(v_behavior_5600_);
v_res_5605_ = l_Lean_Parser_prattParser(v_kind_5598_, v_tables_5599_, v_behavior_boxed_5604_, v_antiquotParser_5601_, v_c_5602_, v_s_5603_);
return v_res_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5610_, lean_object* v_s_5611_){
_start:
{
lean_object* v_toInputContext_5612_; lean_object* v_pos_5613_; lean_object* v_inputString_5614_; lean_object* v___f_5615_; lean_object* v_initStackSz_5616_; uint32_t v_curr_5621_; uint8_t v___y_5623_; uint32_t v___x_5629_; uint8_t v___x_5630_; 
v_toInputContext_5612_ = lean_ctor_get(v_c_5610_, 0);
v_pos_5613_ = lean_ctor_get(v_s_5611_, 2);
lean_inc(v_pos_5613_);
v_inputString_5614_ = lean_ctor_get(v_toInputContext_5612_, 0);
v___f_5615_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_initStackSz_5616_ = l_Lean_Parser_ParserState_stackSize(v_s_5611_);
v_curr_5621_ = lean_string_utf8_get(v_inputString_5614_, v_pos_5613_);
v___x_5629_ = 48;
v___x_5630_ = lean_uint32_dec_le(v___x_5629_, v_curr_5621_);
if (v___x_5630_ == 0)
{
v___y_5623_ = v___x_5630_;
goto v___jp_5622_;
}
else
{
uint32_t v___x_5631_; uint8_t v___x_5632_; 
v___x_5631_ = 57;
v___x_5632_ = lean_uint32_dec_le(v_curr_5621_, v___x_5631_);
v___y_5623_ = v___x_5632_;
goto v___jp_5622_;
}
v___jp_5617_:
{
lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; 
v___x_5618_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5619_, 0, v_initStackSz_5616_);
v___x_5620_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5611_, v___x_5618_, v_pos_5613_, v___x_5619_);
lean_dec_ref(v___x_5619_);
return v___x_5620_;
}
v___jp_5622_:
{
if (v___y_5623_ == 0)
{
lean_dec_ref(v_c_5610_);
goto v___jp_5617_;
}
else
{
uint32_t v___x_5624_; uint8_t v___x_5625_; 
v___x_5624_ = 48;
v___x_5625_ = lean_uint32_dec_eq(v_curr_5621_, v___x_5624_);
if (v___x_5625_ == 0)
{
lean_object* v_s_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
lean_dec(v_initStackSz_5616_);
v_s_5626_ = l_Lean_Parser_takeWhileFn(v___f_5615_, v_c_5610_, v_s_5611_);
v___x_5627_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5628_ = l_Lean_Parser_mkNodeToken(v___x_5627_, v_pos_5613_, v___y_5623_, v_c_5610_, v_s_5626_);
return v___x_5628_;
}
else
{
lean_dec_ref(v_c_5610_);
goto v___jp_5617_;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5633_; uint8_t v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v___x_5633_ = 0;
v___x_5634_ = 1;
v___x_5635_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5636_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5637_ = l_Lean_Parser_mkAntiquot(v___x_5636_, v___x_5635_, v___x_5634_, v___x_5633_);
return v___x_5637_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5638_; lean_object* v___x_5639_; 
v___x_5638_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5639_ = l_Lean_Parser_mkAtomicInfo(v___x_5638_);
return v___x_5639_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5640_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5641_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
lean_ctor_set(v___x_5642_, 1, v___x_5640_);
return v___x_5642_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; 
v___x_5643_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5644_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5645_ = l_Lean_Parser_withAntiquot(v___x_5644_, v___x_5643_);
return v___x_5645_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5646_; 
v___x_5646_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5647_, lean_object* v_s_5648_){
_start:
{
lean_inc_ref(v_s_5648_);
return v_s_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5649_, lean_object* v_s_5650_){
_start:
{
lean_object* v_res_5651_; 
v_res_5651_ = l_Lean_Parser_skip___lam__0(v_x_5649_, v_s_5650_);
lean_dec_ref(v_s_5650_);
lean_dec_ref(v_x_5649_);
return v_res_5651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5657_, lean_object* v_s_5658_, lean_object* v_f_5659_, lean_object* v_b_5660_){
_start:
{
lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; uint8_t v___x_5664_; 
v___x_5661_ = l_Lean_Syntax_getArgs(v_s_5658_);
v___x_5662_ = lean_unsigned_to_nat(0u);
v___x_5663_ = lean_array_get_size(v___x_5661_);
v___x_5664_ = lean_nat_dec_lt(v___x_5662_, v___x_5663_);
if (v___x_5664_ == 0)
{
lean_object* v_toApplicative_5665_; lean_object* v_toPure_5666_; lean_object* v___x_5667_; 
lean_dec_ref(v___x_5661_);
lean_dec(v_f_5659_);
v_toApplicative_5665_ = lean_ctor_get(v_inst_5657_, 0);
lean_inc_ref(v_toApplicative_5665_);
lean_dec_ref(v_inst_5657_);
v_toPure_5666_ = lean_ctor_get(v_toApplicative_5665_, 1);
lean_inc(v_toPure_5666_);
lean_dec_ref(v_toApplicative_5665_);
v___x_5667_ = lean_apply_2(v_toPure_5666_, lean_box(0), v_b_5660_);
return v___x_5667_;
}
else
{
lean_object* v___x_5668_; uint8_t v___x_5669_; 
v___x_5668_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5668_, 0, lean_box(0));
lean_closure_set(v___x_5668_, 1, lean_box(0));
lean_closure_set(v___x_5668_, 2, lean_box(0));
lean_closure_set(v___x_5668_, 3, v_f_5659_);
v___x_5669_ = lean_nat_dec_le(v___x_5663_, v___x_5663_);
if (v___x_5669_ == 0)
{
if (v___x_5664_ == 0)
{
lean_object* v_toApplicative_5670_; lean_object* v_toPure_5671_; lean_object* v___x_5672_; 
lean_dec_ref(v___x_5668_);
lean_dec_ref(v___x_5661_);
v_toApplicative_5670_ = lean_ctor_get(v_inst_5657_, 0);
lean_inc_ref(v_toApplicative_5670_);
lean_dec_ref(v_inst_5657_);
v_toPure_5671_ = lean_ctor_get(v_toApplicative_5670_, 1);
lean_inc(v_toPure_5671_);
lean_dec_ref(v_toApplicative_5670_);
v___x_5672_ = lean_apply_2(v_toPure_5671_, lean_box(0), v_b_5660_);
return v___x_5672_;
}
else
{
size_t v___x_5673_; size_t v___x_5674_; lean_object* v___x_5675_; 
v___x_5673_ = ((size_t)0ULL);
v___x_5674_ = lean_usize_of_nat(v___x_5663_);
v___x_5675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5657_, v___x_5668_, v___x_5661_, v___x_5673_, v___x_5674_, v_b_5660_);
return v___x_5675_;
}
}
else
{
size_t v___x_5676_; size_t v___x_5677_; lean_object* v___x_5678_; 
v___x_5676_ = ((size_t)0ULL);
v___x_5677_ = lean_usize_of_nat(v___x_5663_);
v___x_5678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5657_, v___x_5668_, v___x_5661_, v___x_5676_, v___x_5677_, v_b_5660_);
return v___x_5678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5679_, lean_object* v_s_5680_, lean_object* v_f_5681_, lean_object* v_b_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5679_, v_s_5680_, v_f_5681_, v_b_5682_);
lean_dec(v_s_5680_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5684_, lean_object* v_inst_5685_, lean_object* v_00_u03b2_5686_, lean_object* v_s_5687_, lean_object* v_f_5688_, lean_object* v_b_5689_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5685_, v_s_5687_, v_f_5688_, v_b_5689_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5691_, lean_object* v_inst_5692_, lean_object* v_00_u03b2_5693_, lean_object* v_s_5694_, lean_object* v_f_5695_, lean_object* v_b_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l_Lean_Syntax_foldArgsM(v_m_5691_, v_inst_5692_, v_00_u03b2_5693_, v_s_5694_, v_f_5695_, v_b_5696_);
lean_dec(v_s_5694_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5698_, lean_object* v_x1_5699_, lean_object* v_x2_5700_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = lean_apply_2(v_f_5698_, v_x1_5699_, v_x2_5700_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5702_, lean_object* v_as_5703_, size_t v_i_5704_, size_t v_stop_5705_, lean_object* v_b_5706_){
_start:
{
uint8_t v___x_5707_; 
v___x_5707_ = lean_usize_dec_eq(v_i_5704_, v_stop_5705_);
if (v___x_5707_ == 0)
{
lean_object* v___x_5708_; lean_object* v___x_5709_; size_t v___x_5710_; size_t v___x_5711_; 
v___x_5708_ = lean_array_uget_borrowed(v_as_5703_, v_i_5704_);
lean_inc(v_f_5702_);
lean_inc(v___x_5708_);
v___x_5709_ = lean_apply_2(v_f_5702_, v___x_5708_, v_b_5706_);
v___x_5710_ = ((size_t)1ULL);
v___x_5711_ = lean_usize_add(v_i_5704_, v___x_5710_);
v_i_5704_ = v___x_5711_;
v_b_5706_ = v___x_5709_;
goto _start;
}
else
{
lean_dec(v_f_5702_);
return v_b_5706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5713_, lean_object* v_as_5714_, lean_object* v_i_5715_, lean_object* v_stop_5716_, lean_object* v_b_5717_){
_start:
{
size_t v_i_boxed_5718_; size_t v_stop_boxed_5719_; lean_object* v_res_5720_; 
v_i_boxed_5718_ = lean_unbox_usize(v_i_5715_);
lean_dec(v_i_5715_);
v_stop_boxed_5719_ = lean_unbox_usize(v_stop_5716_);
lean_dec(v_stop_5716_);
v_res_5720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5713_, v_as_5714_, v_i_boxed_5718_, v_stop_boxed_5719_, v_b_5717_);
lean_dec_ref(v_as_5714_);
return v_res_5720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5721_, lean_object* v_f_5722_, lean_object* v_b_5723_){
_start:
{
lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; uint8_t v___x_5727_; 
v___x_5724_ = l_Lean_Syntax_getArgs(v_s_5721_);
v___x_5725_ = lean_unsigned_to_nat(0u);
v___x_5726_ = lean_array_get_size(v___x_5724_);
v___x_5727_ = lean_nat_dec_lt(v___x_5725_, v___x_5726_);
if (v___x_5727_ == 0)
{
lean_dec_ref(v___x_5724_);
lean_dec(v_f_5722_);
return v_b_5723_;
}
else
{
uint8_t v___x_5728_; 
v___x_5728_ = lean_nat_dec_le(v___x_5726_, v___x_5726_);
if (v___x_5728_ == 0)
{
if (v___x_5727_ == 0)
{
lean_dec_ref(v___x_5724_);
lean_dec(v_f_5722_);
return v_b_5723_;
}
else
{
size_t v___x_5729_; size_t v___x_5730_; lean_object* v___x_5731_; 
v___x_5729_ = ((size_t)0ULL);
v___x_5730_ = lean_usize_of_nat(v___x_5726_);
v___x_5731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5722_, v___x_5724_, v___x_5729_, v___x_5730_, v_b_5723_);
lean_dec_ref(v___x_5724_);
return v___x_5731_;
}
}
else
{
size_t v___x_5732_; size_t v___x_5733_; lean_object* v___x_5734_; 
v___x_5732_ = ((size_t)0ULL);
v___x_5733_ = lean_usize_of_nat(v___x_5726_);
v___x_5734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5722_, v___x_5724_, v___x_5732_, v___x_5733_, v_b_5723_);
lean_dec_ref(v___x_5724_);
return v___x_5734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5735_, lean_object* v_f_5736_, lean_object* v_b_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5735_, v_f_5736_, v_b_5737_);
lean_dec(v_s_5735_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5739_, lean_object* v_f_5740_, lean_object* v_b_5741_){
_start:
{
lean_object* v___f_5742_; lean_object* v___x_5743_; 
v___f_5742_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5742_, 0, v_f_5740_);
v___x_5743_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5739_, v___f_5742_, v_b_5741_);
return v___x_5743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_5744_, lean_object* v_f_5745_, lean_object* v_b_5746_){
_start:
{
lean_object* v_res_5747_; 
v_res_5747_ = l_Lean_Syntax_foldArgs___redArg(v_s_5744_, v_f_5745_, v_b_5746_);
lean_dec(v_s_5744_);
return v_res_5747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_5748_, lean_object* v_s_5749_, lean_object* v_f_5750_, lean_object* v_b_5751_){
_start:
{
lean_object* v___x_5752_; 
v___x_5752_ = l_Lean_Syntax_foldArgs___redArg(v_s_5749_, v_f_5750_, v_b_5751_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_5753_, lean_object* v_s_5754_, lean_object* v_f_5755_, lean_object* v_b_5756_){
_start:
{
lean_object* v_res_5757_; 
v_res_5757_ = l_Lean_Syntax_foldArgs(v_00_u03b2_5753_, v_s_5754_, v_f_5755_, v_b_5756_);
lean_dec(v_s_5754_);
return v_res_5757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_5758_, lean_object* v_s_5759_, lean_object* v_f_5760_, lean_object* v_b_5761_){
_start:
{
lean_object* v___x_5762_; 
v___x_5762_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5759_, v_f_5760_, v_b_5761_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_5763_, lean_object* v_s_5764_, lean_object* v_f_5765_, lean_object* v_b_5766_){
_start:
{
lean_object* v_res_5767_; 
v_res_5767_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_5763_, v_s_5764_, v_f_5765_, v_b_5766_);
lean_dec(v_s_5764_);
return v_res_5767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_5768_, lean_object* v_f_5769_, lean_object* v_as_5770_, size_t v_i_5771_, size_t v_stop_5772_, lean_object* v_b_5773_){
_start:
{
lean_object* v___x_5774_; 
v___x_5774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5769_, v_as_5770_, v_i_5771_, v_stop_5772_, v_b_5773_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5775_, lean_object* v_f_5776_, lean_object* v_as_5777_, lean_object* v_i_5778_, lean_object* v_stop_5779_, lean_object* v_b_5780_){
_start:
{
size_t v_i_boxed_5781_; size_t v_stop_boxed_5782_; lean_object* v_res_5783_; 
v_i_boxed_5781_ = lean_unbox_usize(v_i_5778_);
lean_dec(v_i_5778_);
v_stop_boxed_5782_ = lean_unbox_usize(v_stop_5779_);
lean_dec(v_stop_5779_);
v_res_5783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_5775_, v_f_5776_, v_as_5777_, v_i_boxed_5781_, v_stop_boxed_5782_, v_b_5780_);
lean_dec_ref(v_as_5777_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_5784_, lean_object* v_s_5785_, lean_object* v_x_5786_){
_start:
{
lean_object* v___x_5787_; 
v___x_5787_ = lean_apply_1(v_f_5784_, v_s_5785_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_5788_, lean_object* v_s_5789_, lean_object* v_f_5790_){
_start:
{
lean_object* v___f_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; 
v___f_5791_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5791_, 0, v_f_5790_);
v___x_5792_ = lean_box(0);
v___x_5793_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5788_, v_s_5789_, v___f_5791_, v___x_5792_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_5794_, lean_object* v_s_5795_, lean_object* v_f_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Lean_Syntax_forArgsM___redArg(v_inst_5794_, v_s_5795_, v_f_5796_);
lean_dec(v_s_5795_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_5798_, lean_object* v_inst_5799_, lean_object* v_s_5800_, lean_object* v_f_5801_){
_start:
{
lean_object* v___x_5802_; 
v___x_5802_ = l_Lean_Syntax_forArgsM___redArg(v_inst_5799_, v_s_5800_, v_f_5801_);
return v___x_5802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_5803_, lean_object* v_inst_5804_, lean_object* v_s_5805_, lean_object* v_f_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l_Lean_Syntax_forArgsM(v_m_5803_, v_inst_5804_, v_s_5805_, v_f_5806_);
lean_dec(v_s_5805_);
return v_res_5807_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_numLitNoAntiquot = _init_l_Lean_Parser_numLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot);
l_Lean_Parser_hexnumNoAntiquot = _init_l_Lean_Parser_hexnumNoAntiquot();
lean_mark_persistent(l_Lean_Parser_hexnumNoAntiquot);
l_Lean_Parser_scientificLitNoAntiquot = _init_l_Lean_Parser_scientificLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot);
l_Lean_Parser_strLitNoAntiquot = _init_l_Lean_Parser_strLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot);
l_Lean_Parser_charLitNoAntiquot = _init_l_Lean_Parser_charLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot);
l_Lean_Parser_nameLitNoAntiquot = _init_l_Lean_Parser_nameLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot);
l_Lean_Parser_identNoAntiquot = _init_l_Lean_Parser_identNoAntiquot();
lean_mark_persistent(l_Lean_Parser_identNoAntiquot);
l_Lean_Parser_hygieneInfoNoAntiquot = _init_l_Lean_Parser_hygieneInfoNoAntiquot();
lean_mark_persistent(l_Lean_Parser_hygieneInfoNoAntiquot);
res = l_Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_eoi = _init_l_Lean_Parser_eoi();
lean_mark_persistent(l_Lean_Parser_eoi);
l_Lean_Parser_instInhabitedLeadingIdentBehavior_default = _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default();
l_Lean_Parser_instInhabitedLeadingIdentBehavior = _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior();
l_Lean_Parser_instInhabitedParserCategory_default = _init_l_Lean_Parser_instInhabitedParserCategory_default();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory_default);
l_Lean_Parser_instInhabitedParserCategory = _init_l_Lean_Parser_instInhabitedParserCategory();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnRef);
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension);
lean_dec_ref(res);
res = l_Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_antiquotNestedExpr = _init_l_Lean_Parser_antiquotNestedExpr();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr);
l_Lean_Parser_antiquotExpr = _init_l_Lean_Parser_antiquotExpr();
lean_mark_persistent(l_Lean_Parser_antiquotExpr);
res = l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_fieldIdx = _init_l_Lean_Parser_fieldIdx();
lean_mark_persistent(l_Lean_Parser_fieldIdx);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
