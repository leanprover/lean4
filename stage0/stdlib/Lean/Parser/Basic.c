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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "errorAtSavedPos"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 209, 12, 134, 87, 184, 144, 74)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "Generate an error at the position saved with the `withPosition` combinator.\nIf `delta == true`, then it reports at saved position+1.\nThis useful to make sure a parser consumed at least one character.  "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 70, 47, 117, 238, 126, 239, 49)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 322, .m_capacity = 322, .m_length = 321, .m_data = "Run `p`, falling back to `q` if `p` failed without consuming any input.\n\nNOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser\nproducing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`\nis fine as well. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instOrElseParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instOrElseParser___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instOrElseParser___closed__0 = (const lean_object*)&l_Lean_Parser_instOrElseParser___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instOrElseParser = (const lean_object*)&l_Lean_Parser_instOrElseParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 16, 254, 130, 153, 255, 99, 153)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 459, .m_capacity = 459, .m_length = 458, .m_data = "The `atomic(p)` parser parses `p`, returns the same result as `p` and fails iff `p` fails,\nbut if `p` fails after consuming some tokens `atomic(p)` will fail without consuming tokens.\nThis is important for the `p <|> q` combinator, because it is not backtracking, and will fail if\n`p` fails after consuming some tokens. To get backtracking behavior, use `atomic(p) <|> q` instead.\n\nThis parser has the same arity as `p` - it produces the same result as `p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "recover'"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 86, 208, 93, 10, 1, 153, 43)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 455, .m_capacity = 455, .m_length = 454, .m_data = "Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is provided with information about the failing parser's effects , and it is run in the\nstate immediately after the failure.\n\nThe interactions between <|> and `recover'` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 137, 49, 69, 62, 133, 213, 34)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 381, .m_capacity = 381, .m_length = 380, .m_data = "Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is run in the state immediately after the failure.\n\nThe interactions between <|> and `recover` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_optionalFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_optionalFn___closed__0 = (const lean_object*)&l_Lean_Parser_optionalFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_optionalFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_optionalFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_optionalFn___closed__1 = (const lean_object*)&l_Lean_Parser_optionalFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lookahead"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 19, 60, 201, 90, 143, 111, 211)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 310, .m_capacity = 310, .m_length = 309, .m_data = "`lookahead(p)` runs `p` and fails if `p` does, but it produces no parse nodes and rewinds the\nposition to the original state on success. So for example `lookahead(\"=>\")` will ensure that the\nnext token is `\"=>\"`, without actually consuming this token.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_notFollowedByFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unexpected "};
static const lean_object* l_Lean_Parser_notFollowedByFn___closed__0 = (const lean_object*)&l_Lean_Parser_notFollowedByFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "notFollowedBy"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 0, 133, 48, 146, 73, 208, 113)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 175, .m_capacity = 175, .m_length = 174, .m_data = "`notFollowedBy(p, \"foo\")` succeeds iff `p` fails;\nif `p` succeeds then it fails with the message `\"unexpected foo\"`.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "checkWsBefore"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 180, 243, 53, 77, 82, 55, 205)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 216, .m_capacity = 216, .m_length = 215, .m_data = "The `ws` parser requires that there is some whitespace at this location.\nFor example, the parser `\"foo\" ws \"+\"` parses `foo +` or `foo/- -/+` but not `foo+`.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "checkLinebreakBefore"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 136, 117, 184, 203, 101, 193, 45)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 188, .m_capacity = 188, .m_length = 187, .m_data = "The `linebreak` parser requires that there is at least one line break at this location.\n(The line break may be inside a comment.)\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkNoWsBefore"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 175, 148, 38, 136, 238, 167, 124)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 413, .m_capacity = 413, .m_length = 412, .m_data = "The `noWs` parser requires that there is *no* whitespace between the preceding and following\nparsers. For example, the parser `\"foo\" noWs \"+\"` parses `foo+` but not `foo +`.\n\nThis is almost the same as `\"foo+\"`, but using this parser will make `foo+` a token, which may cause\nproblems for the use of `\"foo\"` and `\"+\"` as separate tokens in other parsers.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColEq"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 79, 136, 97, 27, 86, 56, 4)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 299, .m_capacity = 299, .m_length = 298, .m_data = "The `colEq` parser ensures that the next token starts at exactly the column of the saved\nposition (see `withPosition`). This can be used to do whitespace sensitive syntax like\na `by` block or `do` block, where all the lines have to line up.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGe"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 21, 222, 233, 68, 88, 239, 150)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 474, .m_capacity = 474, .m_length = 473, .m_data = "The `colGe` parser requires that the next token starts from at least the column of the saved\nposition (see `withPosition`), but allows it to be more indented.\nThis can be used for whitespace sensitive syntax to ensure that a block does not go outside a\ncertain indentation scope. For example it is used in the lean grammar for `else if`, to ensure\nthat the `else` is not less indented than the `if` it matches with.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGt"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 27, 6, 116, 51, 223, 220, 245)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 572, .m_capacity = 572, .m_length = 571, .m_data = "The `colGt` parser requires that the next token starts a strictly greater column than the saved\nposition (see `withPosition`). This can be used for whitespace sensitive syntax for the arguments\nto a tactic, to ensure that the following tactic is not interpreted as an argument.\n```\nexample (x : False) : False := by\n  revert x\n  exact id\n```\nHere, the `revert` tactic is followed by a list of `colGt ident`, because otherwise it would\ninterpret `exact` as an identifier and try to revert a variable named `exact`.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checkLineEq"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 130, 255, 142, 22, 38, 200, 197)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 367, .m_capacity = 367, .m_length = 366, .m_data = "The `lineEq` parser requires that the current token is on the same line as the saved position\n(see `withPosition`). This can be used to ensure that composite tokens are not \"broken up\" across\ndifferent lines. For example, `else if` is parsed using `lineEq` to ensure that the two tokens\nare on the same line.\n\nThis parser has arity 0 - it does not capture anything. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 188, 255, 221, 143, 31, 128, 82)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 761, .m_capacity = 761, .m_length = 760, .m_data = "`withPosition(p)` runs `p` while setting the \"saved position\" to the current position.\nThis has no effect on its own, but various other parsers access this position to achieve some\ncomposite effect:\n\n* `colGt`, `colGe`, `colEq` compare the column of the saved position to the current position,\n  used to implement Python-style indentation sensitive blocks\n* `lineEq` ensures that the current position is still on the same line as the saved position,\n  used to implement composite tokens\n\nThe saved position is only available in the read-only state, which is why this is a scoping parser:\nafter the `withPosition(..)` block the saved position will be restored to its original value.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_withoutPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_withoutPosition___closed__0 = (const lean_object*)&l_Lean_Parser_withoutPosition___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 222, 221, 61, 47, 46, 252, 242)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 331, .m_capacity = 331, .m_length = 330, .m_data = "`withoutPosition(p)` runs `p` without the saved position, meaning that position-checking\nparsers like `colGt` will have no effect. This is usually used by bracketing constructs like\n`(...)` so that the user can locally override whitespace sensitivity.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withForbidden"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 169, 160, 142, 191, 14, 119, 146)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 497, .m_capacity = 497, .m_length = 496, .m_data = "`withForbidden tk p` runs `p` with `tk` as a \"forbidden token\". This means that if the token\nappears anywhere in `p` (unless it is nested in `withoutForbidden`), parsing will immediately\nstop there, making `tk` effectively a lowest-precedence operator. This is used for parsers like\n`for x in arr do ...`: `arr` is parsed as `withForbidden \"do\" term` because otherwise `arr do ...`\nwould be treated as an application.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withForbiddens___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__0 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__0_value;
static const lean_string_object l_Lean_Parser_withForbiddens___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__1 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__2 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__2_value;
static const lean_array_object l_Lean_Parser_withForbiddens___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__3 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__3_value;
static const lean_string_object l_Lean_Parser_withForbiddens___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__4 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__5 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__5_value;
static const lean_string_object l_Lean_Parser_withForbiddens___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__6 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__7 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__7_value;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__8;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__9;
static const lean_string_object l_Lean_Parser_withForbiddens___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__10 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__11 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__11_value;
static const lean_ctor_object l_Lean_Parser_withForbiddens___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Parser_optionalFn___closed__1_value),((lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__3_value)}};
static const lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__12 = (const lean_object*)&l_Lean_Parser_withForbiddens___auto__1___closed__12_value;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__13;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__14;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__15;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__16;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__17;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__18;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__19;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__20;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__21;
static lean_once_cell_t l_Lean_Parser_withForbiddens___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_withForbiddens___auto__1___closed__22;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "withForbiddens"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 28, 48, 51, 203, 186, 28, 196)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 289, .m_capacity = 289, .m_length = 288, .m_data = "`withForbiddens(tks, p)` runs `p` with every token in `tks` treated as forbidden, i.e. the\ncombined effect of nesting `withForbidden` for each token (see `withForbidden`). The tokens in\n`tks` must be distinct.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___boxed(lean_object*);
static const lean_array_object l_Lean_Parser_withoutForbidden___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_withoutForbidden___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_withoutForbidden___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_withoutForbidden___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_withoutForbidden___closed__0 = (const lean_object*)&l_Lean_Parser_withoutForbidden___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withoutForbidden"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 219, 174, 6, 42, 106, 219)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 302, .m_capacity = 302, .m_length = 301, .m_data = "`withoutForbidden(p)` runs `p` disabling the \"forbidden token\" (see `withForbidden`), if any.\nThis is usually used by bracketing constructs like `(...)` because there is no parsing ambiguity\ninside these nested constructs.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_instInhabitedPrattParsingTables___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_instInhabitedPrattParsingTables___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedPrattParsingTables___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedPrattParsingTables = (const lean_object*)&l_Lean_Parser_instInhabitedPrattParsingTables___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "checkNoImmediateColon"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 36, 224, 107, 75, 228, 108, 120)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Fail if previous token is immediately followed by ':'. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkAntiquot"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 252, 121, 56, 15, 15, 211, 216)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 257, .m_capacity = 257, .m_length = 256, .m_data = "Define parser for `$e` (if `anonymous == true`) and `$e:name`.\n`kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.\nAntiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withAntiquot"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 88, 47, 17, 27, 77, 70, 127)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Optimized version of `mkAntiquot ... <|> p`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mkAntiquotSplice"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 175, 234, 39, 152, 246, 57, 50)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Parse `$[p]suffix`, e.g. `$[p],*`. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "antiquot_suffix_splice"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 22, 214, 220, 194, 127, 23, 217)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "withAntiquotSuffixSplice"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 216, 213, 160, 91, 190, 161, 104)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node. "};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object*);
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
lean_dec_ref_known(v_x_8_, 2);
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
lean_dec_ref_known(v_x_24_, 2);
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
lean_dec_ref_known(v_x_24_, 2);
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
lean_dec_ref_known(v_errorMsg_65_, 1);
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
v___x_148_ = 0;
return v___x_148_;
}
}
else
{
if (lean_obj_tag(v_x_146_) == 0)
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v_val_151_; uint8_t v___x_152_; 
v_val_150_ = lean_ctor_get(v_x_145_, 0);
v_val_151_ = lean_ctor_get(v_x_146_, 0);
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
lean_dec(v_x_154_);
lean_dec(v_x_153_);
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
lean_dec(v_errorMsg_162_);
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
lean_dec_ref_known(v_savedPos_x3f_292_, 1);
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
lean_dec_ref_known(v_savedPos_x3f_292_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3));
v___x_330_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4));
v___x_331_ = l_Lean_addBuiltinDocString(v___x_329_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___boxed(lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
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
lean_object* v_prec_414_; lean_object* v_quotDepth_415_; uint8_t v_suppressInsideQuot_416_; lean_object* v_savedPos_x3f_417_; lean_object* v_forbiddenTks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_prec_414_ = lean_ctor_get(v_c_413_, 0);
v_quotDepth_415_ = lean_ctor_get(v_c_413_, 1);
v_suppressInsideQuot_416_ = lean_ctor_get_uint8(v_c_413_, sizeof(void*)*4);
v_savedPos_x3f_417_ = lean_ctor_get(v_c_413_, 2);
v_forbiddenTks_418_ = lean_ctor_get(v_c_413_, 3);
v_isSharedCheck_428_ = !lean_is_exclusive(v_c_413_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v_c_413_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_forbiddenTks_418_);
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
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_forbiddenTks_418_);
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
lean_object* v_prec_447_; lean_object* v_quotDepth_448_; lean_object* v_savedPos_x3f_449_; lean_object* v_forbiddenTks_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_prec_447_ = lean_ctor_get(v_c_446_, 0);
v_quotDepth_448_ = lean_ctor_get(v_c_446_, 1);
v_savedPos_x3f_449_ = lean_ctor_get(v_c_446_, 2);
v_forbiddenTks_450_ = lean_ctor_get(v_c_446_, 3);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_eq(v_quotDepth_448_, v___x_451_);
if (v___x_452_ == 0)
{
return v_c_446_;
}
else
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_inc_ref(v_forbiddenTks_450_);
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
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_forbiddenTks_450_);
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
lean_object* v_val_514_; uint8_t v_decide_515_; 
v_val_514_ = lean_ctor_get(v_errorMsg_508_, 0);
v_decide_515_ = lean_nat_dec_eq(v_pos_506_, v_iniPos_502_);
if (v_decide_515_ == 0)
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
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(lean_object* v_k_530_){
_start:
{
lean_inc(v_k_530_);
return v_k_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg___boxed(lean_object* v_k_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(v_k_531_);
lean_dec(v_k_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_object* v_motive_533_, lean_object* v_ctorIdx_534_, uint8_t v_t_535_, lean_object* v_h_536_, lean_object* v_k_537_){
_start:
{
lean_inc(v_k_537_);
return v_k_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___boxed(lean_object* v_motive_538_, lean_object* v_ctorIdx_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_k_542_){
_start:
{
uint8_t v_t_boxed_543_; lean_object* v_res_544_; 
v_t_boxed_543_ = lean_unbox(v_t_540_);
v_res_544_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(v_motive_538_, v_ctorIdx_539_, v_t_boxed_543_, v_h_541_, v_k_542_);
lean_dec(v_k_542_);
lean_dec(v_ctorIdx_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(lean_object* v_acceptLhs_545_){
_start:
{
lean_inc(v_acceptLhs_545_);
return v_acceptLhs_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg___boxed(lean_object* v_acceptLhs_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(v_acceptLhs_546_);
lean_dec(v_acceptLhs_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_object* v_motive_548_, uint8_t v_t_549_, lean_object* v_h_550_, lean_object* v_acceptLhs_551_){
_start:
{
lean_inc(v_acceptLhs_551_);
return v_acceptLhs_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___boxed(lean_object* v_motive_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_acceptLhs_555_){
_start:
{
uint8_t v_t_boxed_556_; lean_object* v_res_557_; 
v_t_boxed_556_ = lean_unbox(v_t_553_);
v_res_557_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(v_motive_552_, v_t_boxed_556_, v_h_554_, v_acceptLhs_555_);
lean_dec(v_acceptLhs_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(lean_object* v_takeLongest_558_){
_start:
{
lean_inc(v_takeLongest_558_);
return v_takeLongest_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg___boxed(lean_object* v_takeLongest_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(v_takeLongest_559_);
lean_dec(v_takeLongest_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_object* v_motive_561_, uint8_t v_t_562_, lean_object* v_h_563_, lean_object* v_takeLongest_564_){
_start:
{
lean_inc(v_takeLongest_564_);
return v_takeLongest_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___boxed(lean_object* v_motive_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_takeLongest_568_){
_start:
{
uint8_t v_t_boxed_569_; lean_object* v_res_570_; 
v_t_boxed_569_ = lean_unbox(v_t_566_);
v_res_570_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(v_motive_565_, v_t_boxed_569_, v_h_567_, v_takeLongest_568_);
lean_dec(v_takeLongest_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(lean_object* v_merge_571_){
_start:
{
lean_inc(v_merge_571_);
return v_merge_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg___boxed(lean_object* v_merge_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(v_merge_572_);
lean_dec(v_merge_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_object* v_motive_574_, uint8_t v_t_575_, lean_object* v_h_576_, lean_object* v_merge_577_){
_start:
{
lean_inc(v_merge_577_);
return v_merge_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___boxed(lean_object* v_motive_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_merge_581_){
_start:
{
uint8_t v_t_boxed_582_; lean_object* v_res_583_; 
v_t_boxed_582_ = lean_unbox(v_t_579_);
v_res_583_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(v_motive_578_, v_t_boxed_582_, v_h_580_, v_merge_581_);
lean_dec(v_merge_581_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(uint8_t v_x_584_, uint8_t v_y_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_584_);
v___x_587_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_y_585_);
v___x_588_ = lean_nat_dec_eq(v___x_586_, v___x_587_);
lean_dec(v___x_587_);
lean_dec(v___x_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed(lean_object* v_x_589_, lean_object* v_y_590_){
_start:
{
uint8_t v_x_21__boxed_591_; uint8_t v_y_22__boxed_592_; uint8_t v_res_593_; lean_object* v_r_594_; 
v_x_21__boxed_591_ = lean_unbox(v_x_589_);
v_y_22__boxed_592_ = lean_unbox(v_y_590_);
v_res_593_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_21__boxed_591_, v_y_22__boxed_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object* v_stx_600_, lean_object* v_s_601_){
_start:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
lean_inc(v_stx_600_);
v___x_603_ = l_Lean_Syntax_isOfKind(v_stx_600_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Parser_ParserState_pushSyntax(v_s_601_, v_stx_600_);
return v___x_604_;
}
else
{
lean_object* v_stxStack_605_; lean_object* v_lhsPrec_606_; lean_object* v_pos_607_; lean_object* v_cache_608_; lean_object* v_errorMsg_609_; lean_object* v_recoveredErrors_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_628_; 
v_stxStack_605_ = lean_ctor_get(v_s_601_, 0);
v_lhsPrec_606_ = lean_ctor_get(v_s_601_, 1);
v_pos_607_ = lean_ctor_get(v_s_601_, 2);
v_cache_608_ = lean_ctor_get(v_s_601_, 3);
v_errorMsg_609_ = lean_ctor_get(v_s_601_, 4);
v_recoveredErrors_610_ = lean_ctor_get(v_s_601_, 5);
v_isSharedCheck_628_ = !lean_is_exclusive(v_s_601_);
if (v_isSharedCheck_628_ == 0)
{
v___x_612_ = v_s_601_;
v_isShared_613_ = v_isSharedCheck_628_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_recoveredErrors_610_);
lean_inc(v_errorMsg_609_);
lean_inc(v_cache_608_);
lean_inc(v_pos_607_);
lean_inc(v_lhsPrec_606_);
lean_inc(v_stxStack_605_);
lean_dec(v_s_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_628_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_raw_614_; lean_object* v_drop_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_627_; 
v_raw_614_ = lean_ctor_get(v_stxStack_605_, 0);
v_drop_615_ = lean_ctor_get(v_stxStack_605_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_stxStack_605_);
if (v_isSharedCheck_627_ == 0)
{
v___x_617_ = v_stxStack_605_;
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_drop_615_);
lean_inc(v_raw_614_);
lean_dec(v_stxStack_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = l_Lean_Syntax_getArgs(v_stx_600_);
lean_dec(v_stx_600_);
v___x_620_ = l_Array_append___redArg(v_raw_614_, v___x_619_);
lean_dec_ref(v___x_619_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_drop_615_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_622_);
v___x_624_ = v___x_612_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_lhsPrec_606_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_pos_607_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_cache_608_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_errorMsg_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 5, v_recoveredErrors_610_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* v_p_629_, lean_object* v_q_630_, uint8_t v_antiquotBehavior_631_, lean_object* v_c_632_, lean_object* v_s_633_){
_start:
{
lean_object* v_pos_634_; lean_object* v_iniSz_635_; lean_object* v_s_636_; lean_object* v_errorMsg_637_; 
v_pos_634_ = lean_ctor_get(v_s_633_, 2);
lean_inc(v_pos_634_);
v_iniSz_635_ = l_Lean_Parser_ParserState_stackSize(v_s_633_);
lean_inc_ref(v_c_632_);
v_s_636_ = lean_apply_2(v_p_629_, v_c_632_, v_s_633_);
v_errorMsg_637_ = lean_ctor_get(v_s_636_, 4);
lean_inc(v_errorMsg_637_);
if (lean_obj_tag(v_errorMsg_637_) == 0)
{
lean_object* v_stxStack_638_; lean_object* v_pos_639_; lean_object* v_pBack_640_; lean_object* v___y_642_; lean_object* v___y_646_; lean_object* v___y_647_; uint8_t v___y_648_; uint8_t v___y_649_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; uint8_t v___y_661_; uint8_t v___y_662_; uint8_t v___y_668_; uint8_t v___x_685_; uint8_t v___x_686_; 
v_stxStack_638_ = lean_ctor_get(v_s_636_, 0);
lean_inc_ref(v_stxStack_638_);
v_pos_639_ = lean_ctor_get(v_s_636_, 2);
lean_inc(v_pos_639_);
v_pBack_640_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_638_);
lean_dec_ref(v_stxStack_638_);
v___x_685_ = 0;
v___x_686_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_631_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_687_ = l_Lean_Parser_ParserState_stackSize(v_s_636_);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_add(v_iniSz_635_, v___x_688_);
v___x_690_ = lean_nat_dec_eq(v___x_687_, v___x_689_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
if (v___x_690_ == 0)
{
lean_dec(v_pBack_640_);
lean_dec(v_pos_639_);
lean_dec(v_iniSz_635_);
lean_dec(v_pos_634_);
lean_dec_ref(v_c_632_);
lean_dec_ref(v_q_630_);
return v_s_636_;
}
else
{
v___y_668_ = v___x_686_;
goto v___jp_667_;
}
}
else
{
v___y_668_ = v___x_686_;
goto v___jp_667_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = l_Lean_Parser_ParserState_restore(v___y_642_, v_iniSz_635_, v_pos_639_);
lean_dec(v_iniSz_635_);
v___x_644_ = l_Lean_Parser_ParserState_pushSyntax(v___x_643_, v_pBack_640_);
return v___x_644_;
}
v___jp_645_:
{
if (v___y_649_ == 0)
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = l_Lean_Parser_SyntaxStack_back(v___y_647_);
lean_dec_ref(v___y_647_);
lean_inc(v___x_650_);
v___x_651_ = l_Lean_Syntax_isAntiquots(v___x_650_);
if (v___x_651_ == 0)
{
lean_dec(v___x_650_);
v___y_642_ = v___y_646_;
goto v___jp_641_;
}
else
{
if (v___y_648_ == 0)
{
lean_object* v_s_652_; lean_object* v_s_653_; lean_object* v_s_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v_pos_639_);
v_s_652_ = l_Lean_Parser_ParserState_popSyntax(v___y_646_);
v_s_653_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_640_, v_s_652_);
v_s_654_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_650_, v_s_653_);
v___x_655_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_656_ = l_Lean_Parser_ParserState_mkNode(v_s_654_, v___x_655_, v_iniSz_635_);
lean_dec(v_iniSz_635_);
return v___x_656_;
}
else
{
lean_dec(v___x_650_);
v___y_642_ = v___y_646_;
goto v___jp_641_;
}
}
}
else
{
lean_dec_ref(v___y_647_);
v___y_642_ = v___y_646_;
goto v___jp_641_;
}
}
v___jp_657_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_663_ = l_Lean_Parser_ParserState_stackSize(v___y_658_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_iniSz_635_, v___x_664_);
v___x_666_ = lean_nat_dec_eq(v___x_663_, v___x_665_);
lean_dec(v___x_665_);
lean_dec(v___x_663_);
if (v___x_666_ == 0)
{
v___y_646_ = v___y_658_;
v___y_647_ = v___y_659_;
v___y_648_ = v___y_661_;
v___y_649_ = v___y_660_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___y_658_;
v___y_647_ = v___y_659_;
v___y_648_ = v___y_661_;
v___y_649_ = v___y_661_;
goto v___jp_645_;
}
}
else
{
lean_dec_ref(v___y_659_);
v___y_642_ = v___y_658_;
goto v___jp_641_;
}
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
uint8_t v___x_669_; 
lean_inc(v_pBack_640_);
v___x_669_ = l_Lean_Syntax_isAntiquots(v_pBack_640_);
if (v___x_669_ == 0)
{
lean_dec(v_pBack_640_);
lean_dec(v_pos_639_);
lean_dec(v_iniSz_635_);
lean_dec(v_pos_634_);
lean_dec_ref(v_c_632_);
lean_dec_ref(v_q_630_);
return v_s_636_;
}
else
{
lean_object* v_s_670_; lean_object* v_s_671_; lean_object* v_stxStack_672_; lean_object* v_pos_673_; lean_object* v_errorMsg_674_; uint8_t v___x_675_; 
v_s_670_ = l_Lean_Parser_ParserState_restore(v_s_636_, v_iniSz_635_, v_pos_634_);
v_s_671_ = lean_apply_2(v_q_630_, v_c_632_, v_s_670_);
v_stxStack_672_ = lean_ctor_get(v_s_671_, 0);
lean_inc_ref(v_stxStack_672_);
v_pos_673_ = lean_ctor_get(v_s_671_, 2);
lean_inc(v_pos_673_);
v_errorMsg_674_ = lean_ctor_get(v_s_671_, 4);
lean_inc(v_errorMsg_674_);
v___x_675_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_674_, v_errorMsg_637_);
lean_dec(v_errorMsg_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_pos_673_);
lean_dec_ref(v_stxStack_672_);
v___x_676_ = l_Lean_Parser_ParserState_restore(v_s_671_, v_iniSz_635_, v_pos_639_);
lean_dec(v_iniSz_635_);
v___x_677_ = l_Lean_Parser_ParserState_pushSyntax(v___x_676_, v_pBack_640_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_add(v_pos_639_, v___x_678_);
v___x_680_ = lean_nat_dec_le(v___x_679_, v_pos_673_);
lean_dec(v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_nat_add(v_pos_673_, v___x_678_);
lean_dec(v_pos_673_);
v___x_682_ = lean_nat_dec_le(v___x_681_, v_pos_639_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 2;
v___x_684_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_631_, v___x_683_);
if (v___x_684_ == 0)
{
v___y_658_ = v_s_671_;
v___y_659_ = v_stxStack_672_;
v___y_660_ = v___x_675_;
v___y_661_ = v___x_680_;
v___y_662_ = v___x_675_;
goto v___jp_657_;
}
else
{
v___y_658_ = v_s_671_;
v___y_659_ = v_stxStack_672_;
v___y_660_ = v___x_675_;
v___y_661_ = v___x_680_;
v___y_662_ = v___x_680_;
goto v___jp_657_;
}
}
else
{
v___y_658_ = v_s_671_;
v___y_659_ = v_stxStack_672_;
v___y_660_ = v___x_675_;
v___y_661_ = v___x_680_;
v___y_662_ = v___x_682_;
goto v___jp_657_;
}
}
else
{
lean_dec(v_pos_673_);
lean_dec_ref(v_stxStack_672_);
lean_dec(v_pBack_640_);
lean_dec(v_pos_639_);
lean_dec(v_iniSz_635_);
return v_s_671_;
}
}
}
}
else
{
lean_dec(v_pBack_640_);
lean_dec(v_pos_639_);
lean_dec(v_iniSz_635_);
lean_dec(v_pos_634_);
lean_dec_ref(v_c_632_);
lean_dec_ref(v_q_630_);
return v_s_636_;
}
}
}
else
{
lean_object* v_pos_691_; lean_object* v_val_692_; uint8_t v_decide_693_; 
v_pos_691_ = lean_ctor_get(v_s_636_, 2);
lean_inc(v_pos_691_);
v_val_692_ = lean_ctor_get(v_errorMsg_637_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_errorMsg_637_, 1);
v_decide_693_ = lean_nat_dec_eq(v_pos_691_, v_pos_634_);
lean_dec(v_pos_691_);
if (v_decide_693_ == 0)
{
lean_dec(v_val_692_);
lean_dec(v_iniSz_635_);
lean_dec(v_pos_634_);
lean_dec_ref(v_c_632_);
lean_dec_ref(v_q_630_);
return v_s_636_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_inc(v_pos_634_);
v___x_694_ = l_Lean_Parser_ParserState_restore(v_s_636_, v_iniSz_635_, v_pos_634_);
lean_dec(v_iniSz_635_);
v___x_695_ = lean_apply_2(v_q_630_, v_c_632_, v___x_694_);
v___x_696_ = l_Lean_Parser_mergeOrElseErrors(v___x_695_, v_val_692_, v_pos_634_, v_decide_693_);
lean_dec(v_pos_634_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_697_, lean_object* v_q_698_, lean_object* v_antiquotBehavior_699_, lean_object* v_c_700_, lean_object* v_s_701_){
_start:
{
uint8_t v_antiquotBehavior_boxed_702_; lean_object* v_res_703_; 
v_antiquotBehavior_boxed_702_ = lean_unbox(v_antiquotBehavior_699_);
v_res_703_ = l_Lean_Parser_orelseFnCore(v_p_697_, v_q_698_, v_antiquotBehavior_boxed_702_, v_c_700_, v_s_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_704_, lean_object* v_q_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
uint8_t v___x_708_; lean_object* v___x_709_; 
v___x_708_ = 2;
v___x_709_ = l_Lean_Parser_orelseFnCore(v_p_704_, v_q_705_, v___x_708_, v_a_706_, v_a_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_710_, lean_object* v_q_711_){
_start:
{
lean_object* v_collectTokens_712_; lean_object* v_collectKinds_713_; lean_object* v_firstTokens_714_; lean_object* v_collectTokens_715_; lean_object* v_collectKinds_716_; lean_object* v_firstTokens_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_727_; 
v_collectTokens_712_ = lean_ctor_get(v_p_710_, 0);
lean_inc_ref(v_collectTokens_712_);
v_collectKinds_713_ = lean_ctor_get(v_p_710_, 1);
lean_inc_ref(v_collectKinds_713_);
v_firstTokens_714_ = lean_ctor_get(v_p_710_, 2);
lean_inc(v_firstTokens_714_);
lean_dec_ref(v_p_710_);
v_collectTokens_715_ = lean_ctor_get(v_q_711_, 0);
v_collectKinds_716_ = lean_ctor_get(v_q_711_, 1);
v_firstTokens_717_ = lean_ctor_get(v_q_711_, 2);
v_isSharedCheck_727_ = !lean_is_exclusive(v_q_711_);
if (v_isSharedCheck_727_ == 0)
{
v___x_719_ = v_q_711_;
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_firstTokens_717_);
lean_inc(v_collectKinds_716_);
lean_inc(v_collectTokens_715_);
lean_dec(v_q_711_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___f_721_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_721_, 0, v_collectKinds_716_);
lean_closure_set(v___f_721_, 1, v_collectKinds_713_);
v___f_722_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_722_, 0, v_collectTokens_715_);
lean_closure_set(v___f_722_, 1, v_collectTokens_712_);
v___x_723_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_714_, v_firstTokens_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 2, v___x_723_);
lean_ctor_set(v___x_719_, 1, v___f_721_);
lean_ctor_set(v___x_719_, 0, v___f_722_);
v___x_725_ = v___x_719_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___f_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___f_721_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_728_, lean_object* v_p2_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_box(0);
v___x_733_ = lean_apply_1(v_p2_729_, v___x_732_);
v___x_734_ = l_Lean_Parser_orelseFn(v_p1_728_, v___x_733_, v___y_730_, v___y_731_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_737_, lean_object* v_q_738_){
_start:
{
lean_object* v_info_739_; lean_object* v_fn_740_; lean_object* v_info_741_; lean_object* v_fn_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_751_; 
v_info_739_ = lean_ctor_get(v_p_737_, 0);
lean_inc_ref(v_info_739_);
v_fn_740_ = lean_ctor_get(v_p_737_, 1);
lean_inc_ref(v_fn_740_);
lean_dec_ref(v_p_737_);
v_info_741_ = lean_ctor_get(v_q_738_, 0);
v_fn_742_ = lean_ctor_get(v_q_738_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_q_738_);
if (v_isSharedCheck_751_ == 0)
{
v___x_744_ = v_q_738_;
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_fn_742_);
lean_inc(v_info_741_);
lean_dec(v_q_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = l_Lean_Parser_orelseInfo(v_info_739_, v_info_741_);
v___x_747_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_747_, 0, v_fn_740_);
lean_closure_set(v___x_747_, 1, v_fn_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_747_);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_760_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_761_ = l_Lean_addBuiltinDocString(v___x_759_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_764_, lean_object* v_b_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_box(0);
v___x_767_ = lean_apply_1(v_b_765_, v___x_766_);
v___x_768_ = l_Lean_Parser_orelse(v_a_764_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_771_){
_start:
{
lean_object* v_collectTokens_772_; lean_object* v_collectKinds_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_781_; 
v_collectTokens_772_ = lean_ctor_get(v_info_771_, 0);
v_collectKinds_773_ = lean_ctor_get(v_info_771_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_info_771_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_info_771_, 2);
lean_dec(v_unused_782_);
v___x_775_ = v_info_771_;
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_collectKinds_773_);
lean_inc(v_collectTokens_772_);
lean_dec(v_info_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_box(1);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 2, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_collectTokens_772_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_collectKinds_773_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_783_, lean_object* v_c_784_, lean_object* v_s_785_){
_start:
{
lean_object* v_pos_786_; lean_object* v___x_787_; lean_object* v_errorMsg_788_; 
v_pos_786_ = lean_ctor_get(v_s_785_, 2);
lean_inc(v_pos_786_);
v___x_787_ = lean_apply_2(v_p_783_, v_c_784_, v_s_785_);
v_errorMsg_788_ = lean_ctor_get(v___x_787_, 4);
lean_inc(v_errorMsg_788_);
if (lean_obj_tag(v_errorMsg_788_) == 1)
{
lean_object* v_stxStack_789_; lean_object* v_lhsPrec_790_; lean_object* v_cache_791_; lean_object* v_recoveredErrors_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_stxStack_789_ = lean_ctor_get(v___x_787_, 0);
v_lhsPrec_790_ = lean_ctor_get(v___x_787_, 1);
v_cache_791_ = lean_ctor_get(v___x_787_, 3);
v_recoveredErrors_792_ = lean_ctor_get(v___x_787_, 5);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; lean_object* v_unused_801_; 
v_unused_800_ = lean_ctor_get(v___x_787_, 4);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v___x_787_, 2);
lean_dec(v_unused_801_);
v___x_794_ = v___x_787_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_recoveredErrors_792_);
lean_inc(v_cache_791_);
lean_inc(v_lhsPrec_790_);
lean_inc(v_stxStack_789_);
lean_dec(v___x_787_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 2, v_pos_786_);
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_stxStack_789_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_lhsPrec_790_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_pos_786_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_cache_791_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_errorMsg_788_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v_recoveredErrors_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_dec(v_errorMsg_788_);
lean_dec(v_pos_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_802_){
_start:
{
lean_object* v_info_803_; lean_object* v_fn_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_info_803_ = lean_ctor_get(v_p_802_, 0);
v_fn_804_ = lean_ctor_get(v_p_802_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_p_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v_p_802_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_fn_804_);
lean_inc(v_info_803_);
lean_dec(v_p_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_808_, 0, v_fn_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_info_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_821_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_822_ = l_Lean_addBuiltinDocString(v___x_820_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
lean_object* v_initialPos_827_; lean_object* v_initialSize_828_; lean_object* v_initialPos_829_; lean_object* v_initialSize_830_; uint8_t v_decide_831_; 
v_initialPos_827_ = lean_ctor_get(v_x_825_, 0);
v_initialSize_828_ = lean_ctor_get(v_x_825_, 1);
v_initialPos_829_ = lean_ctor_get(v_x_826_, 0);
v_initialSize_830_ = lean_ctor_get(v_x_826_, 1);
v_decide_831_ = lean_nat_dec_eq(v_initialPos_827_, v_initialPos_829_);
if (v_decide_831_ == 0)
{
return v_decide_831_;
}
else
{
uint8_t v___x_832_; 
v___x_832_ = lean_nat_dec_eq(v_initialSize_828_, v_initialSize_830_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_833_, v_x_834_);
lean_dec_ref(v_x_834_);
lean_dec_ref(v_x_833_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_initialPos_841_; lean_object* v_initialSize_842_; lean_object* v_initialPos_843_; lean_object* v_initialSize_844_; uint8_t v_decide_845_; 
v_initialPos_841_ = lean_ctor_get(v_x_839_, 0);
v_initialSize_842_ = lean_ctor_get(v_x_839_, 1);
v_initialPos_843_ = lean_ctor_get(v_x_840_, 0);
v_initialSize_844_ = lean_ctor_get(v_x_840_, 1);
v_decide_845_ = lean_nat_dec_eq(v_initialPos_841_, v_initialPos_843_);
if (v_decide_845_ == 0)
{
return v_decide_845_;
}
else
{
uint8_t v___x_846_; 
v___x_846_ = lean_nat_dec_eq(v_initialSize_842_, v_initialSize_844_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_847_, v_x_848_);
lean_dec_ref(v_x_848_);
lean_dec_ref(v_x_847_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_854_, v_x_855_);
lean_dec_ref(v_x_855_);
lean_dec_ref(v_x_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(14u);
v___x_872_ = lean_nat_to_int(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_unsigned_to_nat(15u);
v___x_886_ = lean_nat_to_int(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_888_ = lean_string_length(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_890_ = lean_nat_to_int(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_893_){
_start:
{
lean_object* v_initialPos_894_; lean_object* v_initialSize_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_933_; 
v_initialPos_894_ = lean_ctor_get(v_x_893_, 0);
v_initialSize_895_ = lean_ctor_get(v_x_893_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_933_ == 0)
{
v___x_897_ = v_x_893_;
v_isShared_898_ = v_isSharedCheck_933_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_initialSize_895_);
lean_inc(v_initialPos_894_);
lean_dec(v_x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_933_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_899_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_900_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_901_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_902_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_903_ = l_Nat_reprFast(v_initialPos_894_);
v___x_904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 5);
lean_ctor_set(v___x_897_, 1, v___x_904_);
lean_ctor_set(v___x_897_, 0, v___x_902_);
v___x_906_ = v___x_897_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_932_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_907_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_901_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = 0;
v___x_911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*1, v___x_910_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_900_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_box(1);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_899_);
v___x_920_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_921_ = l_Nat_reprFast(v_initialSize_895_);
v___x_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___x_923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_920_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*1, v___x_910_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_919_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_927_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_925_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_907_);
v___x_930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_910_);
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_934_, lean_object* v_prec_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_937_, lean_object* v_prec_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_937_, v_prec_938_);
lean_dec(v_prec_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_942_, lean_object* v_recover_943_, lean_object* v_c_944_, lean_object* v_s_945_){
_start:
{
lean_object* v_stxStack_946_; lean_object* v_pos_947_; lean_object* v_s_948_; lean_object* v_errorMsg_949_; 
v_stxStack_946_ = lean_ctor_get(v_s_945_, 0);
lean_inc_ref(v_stxStack_946_);
v_pos_947_ = lean_ctor_get(v_s_945_, 2);
lean_inc(v_pos_947_);
lean_inc_ref(v_c_944_);
v_s_948_ = lean_apply_2(v_p_942_, v_c_944_, v_s_945_);
v_errorMsg_949_ = lean_ctor_get(v_s_948_, 4);
lean_inc(v_errorMsg_949_);
if (lean_obj_tag(v_errorMsg_949_) == 1)
{
lean_object* v_stxStack_950_; lean_object* v_lhsPrec_951_; lean_object* v_pos_952_; lean_object* v_cache_953_; lean_object* v_recoveredErrors_954_; lean_object* v_val_955_; lean_object* v_iniSz_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_s_x27_960_; lean_object* v_stxStack_961_; lean_object* v_pos_962_; lean_object* v_errorMsg_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_974_; 
v_stxStack_950_ = lean_ctor_get(v_s_948_, 0);
lean_inc_ref(v_stxStack_950_);
v_lhsPrec_951_ = lean_ctor_get(v_s_948_, 1);
lean_inc_n(v_lhsPrec_951_, 2);
v_pos_952_ = lean_ctor_get(v_s_948_, 2);
lean_inc(v_pos_952_);
v_cache_953_ = lean_ctor_get(v_s_948_, 3);
lean_inc_ref_n(v_cache_953_, 2);
v_recoveredErrors_954_ = lean_ctor_get(v_s_948_, 5);
lean_inc_ref_n(v_recoveredErrors_954_, 2);
v_val_955_ = lean_ctor_get(v_errorMsg_949_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v_errorMsg_949_, 1);
v_iniSz_956_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_946_);
lean_dec_ref(v_stxStack_946_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_pos_947_);
lean_ctor_set(v___x_957_, 1, v_iniSz_956_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_959_, 0, v_stxStack_950_);
lean_ctor_set(v___x_959_, 1, v_lhsPrec_951_);
lean_ctor_set(v___x_959_, 2, v_pos_952_);
lean_ctor_set(v___x_959_, 3, v_cache_953_);
lean_ctor_set(v___x_959_, 4, v___x_958_);
lean_ctor_set(v___x_959_, 5, v_recoveredErrors_954_);
v_s_x27_960_ = lean_apply_3(v_recover_943_, v___x_957_, v_c_944_, v___x_959_);
v_stxStack_961_ = lean_ctor_get(v_s_x27_960_, 0);
v_pos_962_ = lean_ctor_get(v_s_x27_960_, 2);
v_errorMsg_963_ = lean_ctor_get(v_s_x27_960_, 4);
v_isSharedCheck_974_ = !lean_is_exclusive(v_s_x27_960_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; lean_object* v_unused_976_; lean_object* v_unused_977_; 
v_unused_975_ = lean_ctor_get(v_s_x27_960_, 5);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_s_x27_960_, 3);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_s_x27_960_, 1);
lean_dec(v_unused_977_);
v___x_965_ = v_s_x27_960_;
v_isShared_966_ = v_isSharedCheck_974_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_errorMsg_963_);
lean_inc(v_pos_962_);
lean_inc(v_stxStack_961_);
lean_dec(v_s_x27_960_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_974_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
uint8_t v___x_967_; 
v___x_967_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_963_, v___x_958_);
lean_dec(v_errorMsg_963_);
if (v___x_967_ == 0)
{
lean_del_object(v___x_965_);
lean_dec(v_pos_962_);
lean_dec_ref(v_stxStack_961_);
lean_dec(v_val_955_);
lean_dec_ref(v_recoveredErrors_954_);
lean_dec_ref(v_cache_953_);
lean_dec(v_lhsPrec_951_);
return v_s_948_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec_ref(v_s_948_);
lean_inc_ref(v_stxStack_961_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_stxStack_961_);
lean_ctor_set(v___x_968_, 1, v_val_955_);
lean_inc(v_pos_962_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_pos_962_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_array_push(v_recoveredErrors_954_, v___x_969_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 5, v___x_970_);
lean_ctor_set(v___x_965_, 4, v___x_958_);
lean_ctor_set(v___x_965_, 3, v_cache_953_);
lean_ctor_set(v___x_965_, 1, v_lhsPrec_951_);
v___x_972_ = v___x_965_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_stxStack_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_lhsPrec_951_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_pos_962_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v_cache_953_);
lean_ctor_set(v_reuseFailAlloc_973_, 4, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_973_, 5, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_dec(v_errorMsg_949_);
lean_dec(v_pos_947_);
lean_dec_ref(v_stxStack_946_);
lean_dec_ref(v_c_944_);
lean_dec_ref(v_recover_943_);
return v_s_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_978_, lean_object* v_s_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_982_; lean_object* v_fn_983_; lean_object* v___x_984_; 
v___x_982_ = lean_apply_1(v_handler_978_, v_s_979_);
v_fn_983_ = lean_ctor_get(v___x_982_, 1);
lean_inc_ref(v_fn_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = lean_apply_2(v_fn_983_, v___y_980_, v___y_981_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_985_, lean_object* v_handler_986_){
_start:
{
lean_object* v_info_987_; lean_object* v_fn_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_997_; 
v_info_987_ = lean_ctor_get(v_parser_985_, 0);
v_fn_988_ = lean_ctor_get(v_parser_985_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_parser_985_);
if (v_isSharedCheck_997_ == 0)
{
v___x_990_ = v_parser_985_;
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_fn_988_);
lean_inc(v_info_987_);
lean_dec(v_parser_985_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___f_992_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_992_, 0, v_handler_986_);
v___x_993_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_993_, 0, v_fn_988_);
lean_closure_set(v___x_993_, 1, v___f_992_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_info_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_1006_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_1007_ = l_Lean_addBuiltinDocString(v___x_1005_, v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_1010_, lean_object* v_x_1011_){
_start:
{
lean_inc_ref(v_handler_1010_);
return v_handler_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Parser_recover___lam__0(v_handler_1012_, v_x_1013_);
lean_dec_ref(v_x_1013_);
lean_dec_ref(v_handler_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1015_, lean_object* v_handler_1016_){
_start:
{
lean_object* v___f_1017_; lean_object* v___x_1018_; 
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1017_, 0, v_handler_1016_);
v___x_1018_ = l_Lean_Parser_recover_x27(v_parser_1015_, v___f_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1027_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1028_ = l_Lean_addBuiltinDocString(v___x_1026_, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1034_, lean_object* v_c_1035_, lean_object* v_s_1036_){
_start:
{
lean_object* v_pos_1037_; lean_object* v_iniSz_1038_; lean_object* v___y_1040_; lean_object* v_s_1043_; lean_object* v_pos_1044_; lean_object* v_errorMsg_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_pos_1037_ = lean_ctor_get(v_s_1036_, 2);
lean_inc(v_pos_1037_);
v_iniSz_1038_ = l_Lean_Parser_ParserState_stackSize(v_s_1036_);
v_s_1043_ = lean_apply_2(v_p_1034_, v_c_1035_, v_s_1036_);
v_pos_1044_ = lean_ctor_get(v_s_1043_, 2);
lean_inc(v_pos_1044_);
v_errorMsg_1045_ = lean_ctor_get(v_s_1043_, 4);
lean_inc(v_errorMsg_1045_);
v___x_1046_ = lean_box(0);
v___x_1047_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1045_, v___x_1046_);
lean_dec(v_errorMsg_1045_);
if (v___x_1047_ == 0)
{
uint8_t v_decide_1048_; 
v_decide_1048_ = lean_nat_dec_eq(v_pos_1044_, v_pos_1037_);
lean_dec(v_pos_1044_);
if (v_decide_1048_ == 0)
{
lean_dec(v_pos_1037_);
v___y_1040_ = v_s_1043_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Parser_ParserState_restore(v_s_1043_, v_iniSz_1038_, v_pos_1037_);
v___y_1040_ = v___x_1049_;
goto v___jp_1039_;
}
}
else
{
lean_dec(v_pos_1044_);
lean_dec(v_pos_1037_);
v___y_1040_ = v_s_1043_;
goto v___jp_1039_;
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1042_ = l_Lean_Parser_ParserState_mkNode(v___y_1040_, v___x_1041_, v_iniSz_1038_);
lean_dec(v_iniSz_1038_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1050_){
_start:
{
lean_object* v_collectTokens_1051_; lean_object* v_collectKinds_1052_; lean_object* v_firstTokens_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_collectTokens_1051_ = lean_ctor_get(v_p_1050_, 0);
v_collectKinds_1052_ = lean_ctor_get(v_p_1050_, 1);
v_firstTokens_1053_ = lean_ctor_get(v_p_1050_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_p_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v_p_1050_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_firstTokens_1053_);
lean_inc(v_collectKinds_1052_);
lean_inc(v_collectTokens_1051_);
lean_dec(v_p_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 2, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_collectTokens_1051_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_collectKinds_1052_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v___x_1057_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1062_){
_start:
{
lean_object* v_info_1063_; lean_object* v_fn_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1073_; 
v_info_1063_ = lean_ctor_get(v_p_1062_, 0);
v_fn_1064_ = lean_ctor_get(v_p_1062_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_p_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1066_ = v_p_1062_;
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_fn_1064_);
lean_inc(v_info_1063_);
lean_dec(v_p_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1068_ = l_Lean_Parser_optionalInfo(v_info_1063_);
v___x_1069_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1069_, 0, v_fn_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1069_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1074_, lean_object* v_c_1075_, lean_object* v_s_1076_){
_start:
{
lean_object* v_pos_1077_; lean_object* v_iniSz_1078_; lean_object* v_s_1079_; lean_object* v_errorMsg_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_pos_1077_ = lean_ctor_get(v_s_1076_, 2);
lean_inc(v_pos_1077_);
v_iniSz_1078_ = l_Lean_Parser_ParserState_stackSize(v_s_1076_);
v_s_1079_ = lean_apply_2(v_p_1074_, v_c_1075_, v_s_1076_);
v_errorMsg_1080_ = lean_ctor_get(v_s_1079_, 4);
lean_inc(v_errorMsg_1080_);
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1080_, v___x_1081_);
lean_dec(v_errorMsg_1080_);
if (v___x_1082_ == 0)
{
lean_dec(v_iniSz_1078_);
lean_dec(v_pos_1077_);
return v_s_1079_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Parser_ParserState_restore(v_s_1079_, v_iniSz_1078_, v_pos_1077_);
lean_dec(v_iniSz_1078_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1084_){
_start:
{
lean_object* v_info_1085_; lean_object* v_fn_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_info_1085_ = lean_ctor_get(v_p_1084_, 0);
v_fn_1086_ = lean_ctor_get(v_p_1084_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_p_1084_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1088_ = v_p_1084_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_fn_1086_);
lean_inc(v_info_1085_);
lean_dec(v_p_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1090_, 0, v_fn_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_info_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1103_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1104_ = l_Lean_addBuiltinDocString(v___x_1102_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1108_, lean_object* v_msg_1109_, lean_object* v_c_1110_, lean_object* v_s_1111_){
_start:
{
lean_object* v_pos_1112_; lean_object* v_iniSz_1113_; lean_object* v_s_1114_; lean_object* v_errorMsg_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_pos_1112_ = lean_ctor_get(v_s_1111_, 2);
lean_inc(v_pos_1112_);
v_iniSz_1113_ = l_Lean_Parser_ParserState_stackSize(v_s_1111_);
v_s_1114_ = lean_apply_2(v_p_1108_, v_c_1110_, v_s_1111_);
v_errorMsg_1115_ = lean_ctor_get(v_s_1114_, 4);
lean_inc(v_errorMsg_1115_);
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1115_, v___x_1116_);
lean_dec(v_errorMsg_1115_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Parser_ParserState_restore(v_s_1114_, v_iniSz_1113_, v_pos_1112_);
lean_dec(v_iniSz_1113_);
return v___x_1118_;
}
else
{
lean_object* v_s_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_s_1119_ = l_Lean_Parser_ParserState_restore(v_s_1114_, v_iniSz_1113_, v_pos_1112_);
lean_dec(v_iniSz_1113_);
v___x_1120_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1121_ = lean_string_append(v___x_1120_, v_msg_1109_);
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1119_, v___x_1121_, v___x_1122_, v___x_1117_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1124_, lean_object* v_msg_1125_, lean_object* v_c_1126_, lean_object* v_s_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Parser_notFollowedByFn(v_p_1124_, v_msg_1125_, v_c_1126_, v_s_1127_);
lean_dec_ref(v_msg_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1129_, lean_object* v_msg_1130_){
_start:
{
lean_object* v_fn_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1140_; 
v_fn_1131_ = lean_ctor_get(v_p_1129_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_p_1129_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v_p_1129_, 0);
lean_dec(v_unused_1141_);
v___x_1133_ = v_p_1129_;
v_isShared_1134_ = v_isSharedCheck_1140_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_fn_1131_);
lean_dec(v_p_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1140_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1136_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1136_, 0, v_fn_1131_);
lean_closure_set(v___x_1136_, 1, v_msg_1130_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1136_);
lean_ctor_set(v___x_1133_, 0, v___x_1135_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1150_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1151_ = l_Lean_addBuiltinDocString(v___x_1149_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1155_, lean_object* v_c_1156_, lean_object* v_s_1157_){
_start:
{
lean_object* v_pos_1158_; lean_object* v_iniSz_1159_; lean_object* v_s_1160_; lean_object* v_pos_1161_; lean_object* v_errorMsg_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_pos_1158_ = lean_ctor_get(v_s_1157_, 2);
lean_inc(v_pos_1158_);
v_iniSz_1159_ = l_Lean_Parser_ParserState_stackSize(v_s_1157_);
lean_inc_ref(v_p_1155_);
lean_inc_ref(v_c_1156_);
v_s_1160_ = lean_apply_2(v_p_1155_, v_c_1156_, v_s_1157_);
v_pos_1161_ = lean_ctor_get(v_s_1160_, 2);
lean_inc(v_pos_1161_);
v_errorMsg_1162_ = lean_ctor_get(v_s_1160_, 4);
lean_inc(v_errorMsg_1162_);
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1162_, v___x_1163_);
lean_dec(v_errorMsg_1162_);
if (v___x_1164_ == 0)
{
uint8_t v_decide_1165_; 
lean_dec_ref(v_c_1156_);
lean_dec_ref(v_p_1155_);
v_decide_1165_ = lean_nat_dec_eq(v_pos_1158_, v_pos_1161_);
lean_dec(v_pos_1161_);
if (v_decide_1165_ == 0)
{
lean_dec(v_iniSz_1159_);
lean_dec(v_pos_1158_);
return v_s_1160_;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Parser_ParserState_restore(v_s_1160_, v_iniSz_1159_, v_pos_1158_);
lean_dec(v_iniSz_1159_);
return v___x_1166_;
}
}
else
{
uint8_t v_decide_1167_; 
v_decide_1167_ = lean_nat_dec_eq(v_pos_1158_, v_pos_1161_);
lean_dec(v_pos_1161_);
lean_dec(v_pos_1158_);
if (v_decide_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_add(v_iniSz_1159_, v___x_1168_);
v___x_1170_ = l_Lean_Parser_ParserState_stackSize(v_s_1160_);
v___x_1171_ = lean_nat_dec_lt(v___x_1169_, v___x_1170_);
lean_dec(v___x_1170_);
lean_dec(v___x_1169_);
if (v___x_1171_ == 0)
{
lean_dec(v_iniSz_1159_);
v_s_1157_ = v_s_1160_;
goto _start;
}
else
{
lean_object* v___x_1173_; lean_object* v_s_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1174_ = l_Lean_Parser_ParserState_mkNode(v_s_1160_, v___x_1173_, v_iniSz_1159_);
lean_dec(v_iniSz_1159_);
v_s_1157_ = v_s_1174_;
goto _start;
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_iniSz_1159_);
lean_dec_ref(v_c_1156_);
lean_dec_ref(v_p_1155_);
v___x_1176_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1177_ = lean_box(0);
v___x_1178_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1160_, v___x_1176_, v___x_1177_, v___x_1164_);
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1179_, lean_object* v_c_1180_, lean_object* v_s_1181_){
_start:
{
lean_object* v_iniSz_1182_; lean_object* v_s_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_iniSz_1182_ = l_Lean_Parser_ParserState_stackSize(v_s_1181_);
v_s_1183_ = l_Lean_Parser_manyAux(v_p_1179_, v_c_1180_, v_s_1181_);
v___x_1184_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1185_ = l_Lean_Parser_ParserState_mkNode(v_s_1183_, v___x_1184_, v_iniSz_1182_);
lean_dec(v_iniSz_1182_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1186_){
_start:
{
lean_object* v_info_1187_; lean_object* v_fn_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1197_; 
v_info_1187_ = lean_ctor_get(v_p_1186_, 0);
v_fn_1188_ = lean_ctor_get(v_p_1186_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_p_1186_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1190_ = v_p_1186_;
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_fn_1188_);
lean_inc(v_info_1187_);
lean_dec(v_p_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = l_Lean_Parser_noFirstTokenInfo(v_info_1187_);
v___x_1193_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1193_, 0, v_fn_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1193_);
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1198_, lean_object* v_c_1199_, lean_object* v_s_1200_){
_start:
{
lean_object* v_iniSz_1201_; lean_object* v___x_1202_; lean_object* v_s_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_iniSz_1201_ = l_Lean_Parser_ParserState_stackSize(v_s_1200_);
lean_inc_ref(v_p_1198_);
v___x_1202_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1202_, 0, v_p_1198_);
v_s_1203_ = l_Lean_Parser_andthenFn(v_p_1198_, v___x_1202_, v_c_1199_, v_s_1200_);
v___x_1204_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1205_ = l_Lean_Parser_ParserState_mkNode(v_s_1203_, v___x_1204_, v_iniSz_1201_);
lean_dec(v_iniSz_1201_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1206_){
_start:
{
lean_object* v_info_1207_; lean_object* v_fn_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1216_; 
v_info_1207_ = lean_ctor_get(v_p_1206_, 0);
v_fn_1208_ = lean_ctor_get(v_p_1206_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_p_1206_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1210_ = v_p_1206_;
v_isShared_1211_ = v_isSharedCheck_1216_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_fn_1208_);
lean_inc(v_info_1207_);
lean_dec(v_p_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1216_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1212_, 0, v_fn_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1212_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_info_1207_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1217_, lean_object* v_sep_1218_, uint8_t v_allowTrailingSep_1219_, lean_object* v_iniSz_1220_, uint8_t v_pOpt_1221_, lean_object* v_c_1222_, lean_object* v_s_1223_){
_start:
{
lean_object* v_s_1225_; lean_object* v_pos_1226_; lean_object* v_pos_1243_; lean_object* v_sz_1244_; lean_object* v_s_1245_; lean_object* v_pos_1246_; lean_object* v_errorMsg_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_pos_1243_ = lean_ctor_get(v_s_1223_, 2);
lean_inc(v_pos_1243_);
v_sz_1244_ = l_Lean_Parser_ParserState_stackSize(v_s_1223_);
lean_inc_ref(v_p_1217_);
lean_inc_ref(v_c_1222_);
v_s_1245_ = lean_apply_2(v_p_1217_, v_c_1222_, v_s_1223_);
v_pos_1246_ = lean_ctor_get(v_s_1245_, 2);
lean_inc(v_pos_1246_);
v_errorMsg_1247_ = lean_ctor_get(v_s_1245_, 4);
lean_inc(v_errorMsg_1247_);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1247_, v___x_1248_);
lean_dec(v_errorMsg_1247_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
lean_dec_ref(v_c_1222_);
lean_dec_ref(v_sep_1218_);
lean_dec_ref(v_p_1217_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_pos_1243_, v___x_1250_);
v___x_1252_ = lean_nat_dec_le(v___x_1251_, v_pos_1246_);
lean_dec(v_pos_1246_);
lean_dec(v___x_1251_);
if (v___x_1252_ == 0)
{
if (v_pOpt_1221_ == 0)
{
lean_object* v___x_1253_; lean_object* v_s_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_sz_1244_);
lean_dec(v_pos_1243_);
v___x_1253_ = lean_box(0);
v_s_1254_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1245_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1256_ = l_Lean_Parser_ParserState_mkNode(v_s_1254_, v___x_1255_, v_iniSz_1220_);
return v___x_1256_;
}
else
{
lean_object* v_s_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_s_1257_ = l_Lean_Parser_ParserState_restore(v_s_1245_, v_sz_1244_, v_pos_1243_);
lean_dec(v_sz_1244_);
v___x_1258_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1259_ = l_Lean_Parser_ParserState_mkNode(v_s_1257_, v___x_1258_, v_iniSz_1220_);
return v___x_1259_;
}
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec(v_sz_1244_);
lean_dec(v_pos_1243_);
v___x_1260_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1261_ = l_Lean_Parser_ParserState_mkNode(v_s_1245_, v___x_1260_, v_iniSz_1220_);
return v___x_1261_;
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
lean_dec(v_pos_1243_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v_sz_1244_, v___x_1262_);
v___x_1264_ = l_Lean_Parser_ParserState_stackSize(v_s_1245_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
lean_dec(v___x_1264_);
lean_dec(v___x_1263_);
if (v___x_1265_ == 0)
{
lean_dec(v_sz_1244_);
v_s_1225_ = v_s_1245_;
v_pos_1226_ = v_pos_1246_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1266_; lean_object* v_s_1267_; lean_object* v_pos_1268_; 
lean_dec(v_pos_1246_);
v___x_1266_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1267_ = l_Lean_Parser_ParserState_mkNode(v_s_1245_, v___x_1266_, v_sz_1244_);
lean_dec(v_sz_1244_);
v_pos_1268_ = lean_ctor_get(v_s_1267_, 2);
lean_inc(v_pos_1268_);
v_s_1225_ = v_s_1267_;
v_pos_1226_ = v_pos_1268_;
goto v___jp_1224_;
}
}
v___jp_1224_:
{
lean_object* v_sz_1227_; lean_object* v_s_1228_; lean_object* v_errorMsg_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_sz_1227_ = l_Lean_Parser_ParserState_stackSize(v_s_1225_);
lean_inc_ref(v_sep_1218_);
lean_inc_ref(v_c_1222_);
v_s_1228_ = lean_apply_2(v_sep_1218_, v_c_1222_, v_s_1225_);
v_errorMsg_1229_ = lean_ctor_get(v_s_1228_, 4);
lean_inc(v_errorMsg_1229_);
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1229_, v___x_1230_);
lean_dec(v_errorMsg_1229_);
if (v___x_1231_ == 0)
{
lean_object* v_s_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_c_1222_);
lean_dec_ref(v_sep_1218_);
lean_dec_ref(v_p_1217_);
v_s_1232_ = l_Lean_Parser_ParserState_restore(v_s_1228_, v_sz_1227_, v_pos_1226_);
lean_dec(v_sz_1227_);
v___x_1233_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1234_ = l_Lean_Parser_ParserState_mkNode(v_s_1232_, v___x_1233_, v_iniSz_1220_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
lean_dec(v_pos_1226_);
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_sz_1227_, v___x_1235_);
v___x_1237_ = l_Lean_Parser_ParserState_stackSize(v_s_1228_);
v___x_1238_ = lean_nat_dec_lt(v___x_1236_, v___x_1237_);
lean_dec(v___x_1237_);
lean_dec(v___x_1236_);
if (v___x_1238_ == 0)
{
lean_dec(v_sz_1227_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1219_;
lean_object* _tmp_6 = v_s_1228_;
v_pOpt_1221_ = _tmp_4;
v_s_1223_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1240_; lean_object* v_s_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1241_ = l_Lean_Parser_ParserState_mkNode(v_s_1228_, v___x_1240_, v_sz_1227_);
lean_dec(v_sz_1227_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1219_;
lean_object* _tmp_6 = v_s_1241_;
v_pOpt_1221_ = _tmp_4;
v_s_1223_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1269_, lean_object* v_sep_1270_, lean_object* v_allowTrailingSep_1271_, lean_object* v_iniSz_1272_, lean_object* v_pOpt_1273_, lean_object* v_c_1274_, lean_object* v_s_1275_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1276_; uint8_t v_pOpt_boxed_1277_; lean_object* v_res_1278_; 
v_allowTrailingSep_boxed_1276_ = lean_unbox(v_allowTrailingSep_1271_);
v_pOpt_boxed_1277_ = lean_unbox(v_pOpt_1273_);
v_res_1278_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1269_, v_sep_1270_, v_allowTrailingSep_boxed_1276_, v_iniSz_1272_, v_pOpt_boxed_1277_, v_c_1274_, v_s_1275_);
lean_dec(v_iniSz_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1279_, lean_object* v_sep_1280_, uint8_t v_allowTrailingSep_1281_, lean_object* v_iniSz_1282_, uint8_t v_pOpt_1283_, lean_object* v_c_1284_, lean_object* v_s_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1279_, v_sep_1280_, v_allowTrailingSep_1281_, v_iniSz_1282_, v_pOpt_1283_, v_c_1284_, v_s_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1287_, lean_object* v_sep_1288_, lean_object* v_allowTrailingSep_1289_, lean_object* v_iniSz_1290_, lean_object* v_pOpt_1291_, lean_object* v_c_1292_, lean_object* v_s_1293_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1294_; uint8_t v_pOpt_boxed_1295_; lean_object* v_res_1296_; 
v_allowTrailingSep_boxed_1294_ = lean_unbox(v_allowTrailingSep_1289_);
v_pOpt_boxed_1295_ = lean_unbox(v_pOpt_1291_);
v_res_1296_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1287_, v_sep_1288_, v_allowTrailingSep_boxed_1294_, v_iniSz_1290_, v_pOpt_boxed_1295_, v_c_1292_, v_s_1293_);
lean_dec(v_iniSz_1290_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1297_, lean_object* v_p_1298_, lean_object* v_sep_1299_, lean_object* v_c_1300_, lean_object* v_s_1301_){
_start:
{
lean_object* v_iniSz_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; 
v_iniSz_1302_ = l_Lean_Parser_ParserState_stackSize(v_s_1301_);
v___x_1303_ = 1;
v___x_1304_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1298_, v_sep_1299_, v_allowTrailingSep_1297_, v_iniSz_1302_, v___x_1303_, v_c_1300_, v_s_1301_);
lean_dec(v_iniSz_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1305_, lean_object* v_p_1306_, lean_object* v_sep_1307_, lean_object* v_c_1308_, lean_object* v_s_1309_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1310_; lean_object* v_res_1311_; 
v_allowTrailingSep_boxed_1310_ = lean_unbox(v_allowTrailingSep_1305_);
v_res_1311_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1310_, v_p_1306_, v_sep_1307_, v_c_1308_, v_s_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1312_, lean_object* v_p_1313_, lean_object* v_sep_1314_, lean_object* v_c_1315_, lean_object* v_s_1316_){
_start:
{
lean_object* v_iniSz_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; 
v_iniSz_1317_ = l_Lean_Parser_ParserState_stackSize(v_s_1316_);
v___x_1318_ = 0;
v___x_1319_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1313_, v_sep_1314_, v_allowTrailingSep_1312_, v_iniSz_1317_, v___x_1318_, v_c_1315_, v_s_1316_);
lean_dec(v_iniSz_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1320_, lean_object* v_p_1321_, lean_object* v_sep_1322_, lean_object* v_c_1323_, lean_object* v_s_1324_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1325_; lean_object* v_res_1326_; 
v_allowTrailingSep_boxed_1325_ = lean_unbox(v_allowTrailingSep_1320_);
v_res_1326_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1325_, v_p_1321_, v_sep_1322_, v_c_1323_, v_s_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1327_, lean_object* v_sep_1328_){
_start:
{
lean_object* v_collectTokens_1329_; lean_object* v_collectKinds_1330_; lean_object* v_collectTokens_1331_; lean_object* v_collectKinds_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1342_; 
v_collectTokens_1329_ = lean_ctor_get(v_p_1327_, 0);
lean_inc_ref(v_collectTokens_1329_);
v_collectKinds_1330_ = lean_ctor_get(v_p_1327_, 1);
lean_inc_ref(v_collectKinds_1330_);
lean_dec_ref(v_p_1327_);
v_collectTokens_1331_ = lean_ctor_get(v_sep_1328_, 0);
v_collectKinds_1332_ = lean_ctor_get(v_sep_1328_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_sep_1328_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_sep_1328_, 2);
lean_dec(v_unused_1343_);
v___x_1334_ = v_sep_1328_;
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_collectKinds_1332_);
lean_inc(v_collectTokens_1331_);
lean_dec(v_sep_1328_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___f_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1336_, 0, v_collectKinds_1332_);
lean_closure_set(v___f_1336_, 1, v_collectKinds_1330_);
v___f_1337_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1337_, 0, v_collectTokens_1331_);
lean_closure_set(v___f_1337_, 1, v_collectTokens_1329_);
v___x_1338_ = lean_box(1);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 2, v___x_1338_);
lean_ctor_set(v___x_1334_, 1, v___f_1336_);
lean_ctor_set(v___x_1334_, 0, v___f_1337_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___f_1337_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___f_1336_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1344_, lean_object* v_sep_1345_){
_start:
{
lean_object* v_collectTokens_1346_; lean_object* v_collectKinds_1347_; lean_object* v_firstTokens_1348_; lean_object* v_collectTokens_1349_; lean_object* v_collectKinds_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1359_; 
v_collectTokens_1346_ = lean_ctor_get(v_p_1344_, 0);
lean_inc_ref(v_collectTokens_1346_);
v_collectKinds_1347_ = lean_ctor_get(v_p_1344_, 1);
lean_inc_ref(v_collectKinds_1347_);
v_firstTokens_1348_ = lean_ctor_get(v_p_1344_, 2);
lean_inc(v_firstTokens_1348_);
lean_dec_ref(v_p_1344_);
v_collectTokens_1349_ = lean_ctor_get(v_sep_1345_, 0);
v_collectKinds_1350_ = lean_ctor_get(v_sep_1345_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_sep_1345_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v_sep_1345_, 2);
lean_dec(v_unused_1360_);
v___x_1352_ = v_sep_1345_;
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_collectKinds_1350_);
lean_inc(v_collectTokens_1349_);
lean_dec(v_sep_1345_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___x_1357_; 
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1354_, 0, v_collectKinds_1350_);
lean_closure_set(v___f_1354_, 1, v_collectKinds_1347_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1355_, 0, v_collectTokens_1349_);
lean_closure_set(v___f_1355_, 1, v_collectTokens_1346_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 2, v_firstTokens_1348_);
lean_ctor_set(v___x_1352_, 1, v___f_1354_);
lean_ctor_set(v___x_1352_, 0, v___f_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___f_1355_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___f_1354_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_firstTokens_1348_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1361_, lean_object* v_sep_1362_, uint8_t v_allowTrailingSep_1363_){
_start:
{
lean_object* v_info_1364_; lean_object* v_fn_1365_; lean_object* v_info_1366_; lean_object* v_fn_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
v_info_1364_ = lean_ctor_get(v_p_1361_, 0);
lean_inc_ref(v_info_1364_);
v_fn_1365_ = lean_ctor_get(v_p_1361_, 1);
lean_inc_ref(v_fn_1365_);
lean_dec_ref(v_p_1361_);
v_info_1366_ = lean_ctor_get(v_sep_1362_, 0);
v_fn_1367_ = lean_ctor_get(v_sep_1362_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_sep_1362_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1369_ = v_sep_1362_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_fn_1367_);
lean_inc(v_info_1366_);
lean_dec(v_sep_1362_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1371_ = l_Lean_Parser_sepByInfo(v_info_1364_, v_info_1366_);
v___x_1372_ = lean_box(v_allowTrailingSep_1363_);
v___x_1373_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1373_, 0, v___x_1372_);
lean_closure_set(v___x_1373_, 1, v_fn_1365_);
lean_closure_set(v___x_1373_, 2, v_fn_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v___x_1373_);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1378_, lean_object* v_sep_1379_, lean_object* v_allowTrailingSep_1380_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1381_; lean_object* v_res_1382_; 
v_allowTrailingSep_boxed_1381_ = lean_unbox(v_allowTrailingSep_1380_);
v_res_1382_ = l_Lean_Parser_sepByNoAntiquot(v_p_1378_, v_sep_1379_, v_allowTrailingSep_boxed_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1383_, lean_object* v_sep_1384_, uint8_t v_allowTrailingSep_1385_){
_start:
{
lean_object* v_info_1386_; lean_object* v_fn_1387_; lean_object* v_info_1388_; lean_object* v_fn_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1399_; 
v_info_1386_ = lean_ctor_get(v_p_1383_, 0);
lean_inc_ref(v_info_1386_);
v_fn_1387_ = lean_ctor_get(v_p_1383_, 1);
lean_inc_ref(v_fn_1387_);
lean_dec_ref(v_p_1383_);
v_info_1388_ = lean_ctor_get(v_sep_1384_, 0);
v_fn_1389_ = lean_ctor_get(v_sep_1384_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_sep_1384_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1391_ = v_sep_1384_;
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_fn_1389_);
lean_inc(v_info_1388_);
lean_dec(v_sep_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1393_ = l_Lean_Parser_sepBy1Info(v_info_1386_, v_info_1388_);
v___x_1394_ = lean_box(v_allowTrailingSep_1385_);
v___x_1395_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1395_, 0, v___x_1394_);
lean_closure_set(v___x_1395_, 1, v_fn_1387_);
lean_closure_set(v___x_1395_, 2, v_fn_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v___x_1395_);
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1397_ = v___x_1391_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1400_, lean_object* v_sep_1401_, lean_object* v_allowTrailingSep_1402_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1403_; lean_object* v_res_1404_; 
v_allowTrailingSep_boxed_1403_ = lean_unbox(v_allowTrailingSep_1402_);
v_res_1404_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1400_, v_sep_1401_, v_allowTrailingSep_boxed_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1405_, lean_object* v_f_1406_, lean_object* v_c_1407_, lean_object* v_s_1408_){
_start:
{
lean_object* v_s_1409_; lean_object* v_stxStack_1410_; lean_object* v_errorMsg_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_s_1409_ = lean_apply_2(v_p_1405_, v_c_1407_, v_s_1408_);
v_stxStack_1410_ = lean_ctor_get(v_s_1409_, 0);
lean_inc_ref(v_stxStack_1410_);
v_errorMsg_1411_ = lean_ctor_get(v_s_1409_, 4);
lean_inc(v_errorMsg_1411_);
v___x_1412_ = lean_box(0);
v___x_1413_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1411_, v___x_1412_);
lean_dec(v_errorMsg_1411_);
if (v___x_1413_ == 0)
{
lean_dec_ref(v_stxStack_1410_);
lean_dec_ref(v_f_1406_);
return v_s_1409_;
}
else
{
lean_object* v_stx_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_stx_1414_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1410_);
lean_dec_ref(v_stxStack_1410_);
v___x_1415_ = l_Lean_Parser_ParserState_popSyntax(v_s_1409_);
v___x_1416_ = lean_apply_1(v_f_1406_, v_stx_1414_);
v___x_1417_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1415_, v___x_1416_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1418_){
_start:
{
lean_object* v_collectTokens_1419_; lean_object* v_collectKinds_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_collectTokens_1419_ = lean_ctor_get(v_p_1418_, 0);
v_collectKinds_1420_ = lean_ctor_get(v_p_1418_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_p_1418_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_p_1418_, 2);
lean_dec(v_unused_1429_);
v___x_1422_ = v_p_1418_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_collectKinds_1420_);
lean_inc(v_collectTokens_1419_);
lean_dec(v_p_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_box(1);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 2, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_collectTokens_1419_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_collectKinds_1420_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v___x_1424_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1430_, lean_object* v_f_1431_){
_start:
{
lean_object* v_info_1432_; lean_object* v_fn_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
v_info_1432_ = lean_ctor_get(v_p_1430_, 0);
v_fn_1433_ = lean_ctor_get(v_p_1430_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_p_1430_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1435_ = v_p_1430_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_fn_1433_);
lean_inc(v_info_1432_);
lean_dec(v_p_1430_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1437_ = l_Lean_Parser_withResultOfInfo(v_info_1432_);
v___x_1438_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1438_, 0, v_fn_1433_);
lean_closure_set(v___x_1438_, 1, v_f_1431_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1438_);
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1443_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = l_Lean_Syntax_getNumArgs(v_stx_1443_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_dec_eq(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
if (v___x_1446_ == 0)
{
lean_inc(v_stx_1443_);
return v_stx_1443_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = l_Lean_Syntax_getArg(v_stx_1443_, v___x_1447_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1449_);
lean_dec(v_stx_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1452_){
_start:
{
lean_object* v___f_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___f_1453_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1454_ = l_Lean_Parser_many1NoAntiquot(v_p_1452_);
v___x_1455_ = l_Lean_Parser_withResultOf(v___x_1454_, v___f_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1456_, lean_object* v_errorMsg_1457_, lean_object* v_c_1458_, lean_object* v_s_1459_){
_start:
{
lean_object* v_pos_1460_; lean_object* v_toInputContext_1461_; uint8_t v___x_1462_; 
v_pos_1460_ = lean_ctor_get(v_s_1459_, 2);
v_toInputContext_1461_ = lean_ctor_get(v_c_1458_, 0);
v___x_1462_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1461_, v_pos_1460_);
if (v___x_1462_ == 0)
{
lean_object* v_inputString_1463_; uint32_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_inputString_1463_ = lean_ctor_get(v_toInputContext_1461_, 0);
v___x_1464_ = lean_string_utf8_get_fast(v_inputString_1463_, v_pos_1460_);
v___x_1465_ = lean_box_uint32(v___x_1464_);
v___x_1466_ = lean_apply_1(v_p_1456_, v___x_1465_);
v___x_1467_ = lean_unbox(v___x_1466_);
if (v___x_1467_ == 0)
{
uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = 1;
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1459_, v_errorMsg_1457_, v___x_1469_, v___x_1468_);
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; 
lean_inc(v_pos_1460_);
lean_dec_ref(v_errorMsg_1457_);
v___x_1471_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1459_, v_c_1458_, v_pos_1460_);
lean_dec(v_pos_1460_);
return v___x_1471_;
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v_errorMsg_1457_);
lean_dec_ref(v_p_1456_);
v___x_1472_ = lean_box(0);
v___x_1473_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1459_, v___x_1472_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1474_, lean_object* v_errorMsg_1475_, lean_object* v_c_1476_, lean_object* v_s_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Parser_satisfyFn(v_p_1474_, v_errorMsg_1475_, v_c_1476_, v_s_1477_);
lean_dec_ref(v_c_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1479_, lean_object* v_c_1480_, lean_object* v_s_1481_){
_start:
{
lean_object* v_pos_1482_; lean_object* v_toInputContext_1483_; uint8_t v___x_1484_; 
v_pos_1482_ = lean_ctor_get(v_s_1481_, 2);
v_toInputContext_1483_ = lean_ctor_get(v_c_1480_, 0);
v___x_1484_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1483_, v_pos_1482_);
if (v___x_1484_ == 0)
{
lean_object* v_inputString_1485_; uint32_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_inputString_1485_ = lean_ctor_get(v_toInputContext_1483_, 0);
v___x_1486_ = lean_string_utf8_get_fast(v_inputString_1485_, v_pos_1482_);
v___x_1487_ = lean_box_uint32(v___x_1486_);
lean_inc_ref(v_p_1479_);
v___x_1488_ = lean_apply_1(v_p_1479_, v___x_1487_);
v___x_1489_ = lean_unbox(v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_inc(v_pos_1482_);
v___x_1490_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1481_, v_c_1480_, v_pos_1482_);
lean_dec(v_pos_1482_);
v_s_1481_ = v___x_1490_;
goto _start;
}
else
{
lean_dec_ref(v_p_1479_);
return v_s_1481_;
}
}
else
{
lean_dec_ref(v_p_1479_);
return v_s_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1492_, lean_object* v_c_1493_, lean_object* v_s_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Parser_takeUntilFn(v_p_1492_, v_c_1493_, v_s_1494_);
lean_dec_ref(v_c_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1496_, uint32_t v_c_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_box_uint32(v_c_1497_);
v___x_1499_ = lean_apply_1(v_p_1496_, v___x_1498_);
v___x_1500_ = lean_unbox(v___x_1499_);
if (v___x_1500_ == 0)
{
uint8_t v___x_1501_; 
v___x_1501_ = 1;
return v___x_1501_;
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1503_, lean_object* v_c_1504_){
_start:
{
uint32_t v_c_boxed_1505_; uint8_t v_res_1506_; lean_object* v_r_1507_; 
v_c_boxed_1505_ = lean_unbox_uint32(v_c_1504_);
lean_dec(v_c_1504_);
v_res_1506_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1503_, v_c_boxed_1505_);
v_r_1507_ = lean_box(v_res_1506_);
return v_r_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___f_1511_; lean_object* v___x_1512_; 
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1511_, 0, v_p_1508_);
v___x_1512_ = l_Lean_Parser_takeUntilFn(v___f_1511_, v_a_1509_, v_a_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Parser_takeWhileFn(v_p_1513_, v_a_1514_, v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1517_, lean_object* v_errorMsg_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_inc_ref(v_p_1517_);
v___x_1521_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1521_, 0, v_p_1517_);
lean_closure_set(v___x_1521_, 1, v_errorMsg_1518_);
v___x_1522_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1522_, 0, v_p_1517_);
v___x_1523_ = l_Lean_Parser_andthenFn(v___x_1521_, v___x_1522_, v_a_1519_, v_a_1520_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1525_, lean_object* v_s_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1528_ = lean_box(0);
v___x_1529_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1526_, v___x_1527_, v___x_1528_, v_pushMissingOnError_1525_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1530_, lean_object* v_s_1531_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1532_; lean_object* v_res_1533_; 
v_pushMissingOnError_boxed_1532_ = lean_unbox(v_pushMissingOnError_1530_);
v_res_1533_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1532_, v_s_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1534_, lean_object* v_nesting_1535_, lean_object* v_c_1536_, lean_object* v_s_1537_){
_start:
{
lean_object* v_pos_1538_; lean_object* v_toInputContext_1539_; uint8_t v___x_1540_; 
v_pos_1538_ = lean_ctor_get(v_s_1537_, 2);
v_toInputContext_1539_ = lean_ctor_get(v_c_1536_, 0);
v___x_1540_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1539_, v_pos_1538_);
if (v___x_1540_ == 0)
{
lean_object* v_inputString_1541_; uint32_t v_curr_1542_; lean_object* v_i_1543_; uint32_t v___x_1544_; uint8_t v___x_1545_; 
v_inputString_1541_ = lean_ctor_get(v_toInputContext_1539_, 0);
v_curr_1542_ = lean_string_utf8_get_fast(v_inputString_1541_, v_pos_1538_);
v_i_1543_ = lean_string_utf8_next_fast(v_inputString_1541_, v_pos_1538_);
v___x_1544_ = 45;
v___x_1545_ = lean_uint32_dec_eq(v_curr_1542_, v___x_1544_);
if (v___x_1545_ == 0)
{
uint32_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = 47;
v___x_1547_ = lean_uint32_dec_eq(v_curr_1542_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Parser_ParserState_setPos(v_s_1537_, v_i_1543_);
v_s_1537_ = v___x_1548_;
goto _start;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1539_, v_i_1543_);
if (v___x_1550_ == 0)
{
uint32_t v_curr_1551_; uint8_t v___x_1552_; 
v_curr_1551_ = lean_string_utf8_get_fast(v_inputString_1541_, v_i_1543_);
v___x_1552_ = lean_uint32_dec_eq(v_curr_1551_, v___x_1544_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Parser_ParserState_setPos(v_s_1537_, v_i_1543_);
v_s_1537_ = v___x_1553_;
goto _start;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_nesting_1535_, v___x_1555_);
lean_dec(v_nesting_1535_);
v___x_1557_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1537_, v_c_1536_, v_i_1543_);
v_nesting_1535_ = v___x_1556_;
v_s_1537_ = v___x_1557_;
goto _start;
}
}
else
{
lean_object* v___x_1559_; 
lean_dec(v_nesting_1535_);
v___x_1559_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1534_, v_s_1537_);
return v___x_1559_;
}
}
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1539_, v_i_1543_);
if (v___x_1560_ == 0)
{
uint32_t v_curr_1561_; uint32_t v___x_1562_; uint8_t v___x_1563_; 
v_curr_1561_ = lean_string_utf8_get_fast(v_inputString_1541_, v_i_1543_);
v___x_1562_ = 47;
v___x_1563_ = lean_uint32_dec_eq(v_curr_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Parser_ParserState_setPos(v_s_1537_, v_i_1543_);
v_s_1537_ = v___x_1564_;
goto _start;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_dec_eq(v_nesting_1535_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_nat_sub(v_nesting_1535_, v___x_1566_);
lean_dec(v_nesting_1535_);
v___x_1569_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1537_, v_c_1536_, v_i_1543_);
v_nesting_1535_ = v___x_1568_;
v_s_1537_ = v___x_1569_;
goto _start;
}
else
{
lean_object* v___x_1571_; 
lean_dec(v_nesting_1535_);
v___x_1571_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1537_, v_c_1536_, v_i_1543_);
return v___x_1571_;
}
}
}
else
{
lean_object* v___x_1572_; 
lean_dec(v_nesting_1535_);
v___x_1572_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1534_, v_s_1537_);
return v___x_1572_;
}
}
}
else
{
lean_object* v___x_1573_; 
lean_dec(v_nesting_1535_);
v___x_1573_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1534_, v_s_1537_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1574_, lean_object* v_nesting_1575_, lean_object* v_c_1576_, lean_object* v_s_1577_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1578_; lean_object* v_res_1579_; 
v_pushMissingOnError_boxed_1578_ = lean_unbox(v_pushMissingOnError_1574_);
v_res_1579_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1578_, v_nesting_1575_, v_c_1576_, v_s_1577_);
lean_dec_ref(v_c_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1580_){
_start:
{
uint32_t v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = 10;
v___x_1582_ = lean_uint32_dec_eq(v_c_1580_, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1583_){
_start:
{
uint32_t v_c_boxed_1584_; uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_c_boxed_1584_ = lean_unbox_uint32(v_c_1583_);
lean_dec(v_c_1583_);
v_res_1585_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1584_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1592_, lean_object* v_s_1593_){
_start:
{
lean_object* v_pos_1594_; lean_object* v_toInputContext_1598_; uint8_t v___x_1599_; 
v_pos_1594_ = lean_ctor_get(v_s_1593_, 2);
v_toInputContext_1598_ = lean_ctor_get(v_c_1592_, 0);
v___x_1599_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1598_, v_pos_1594_);
if (v___x_1599_ == 0)
{
lean_object* v_inputString_1600_; uint32_t v_curr_1601_; uint32_t v___x_1602_; uint8_t v___x_1603_; 
v_inputString_1600_ = lean_ctor_get(v_toInputContext_1598_, 0);
v_curr_1601_ = lean_string_utf8_get_fast(v_inputString_1600_, v_pos_1594_);
v___x_1602_ = 9;
v___x_1603_ = lean_uint32_dec_eq(v_curr_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
uint32_t v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = 13;
v___x_1605_ = lean_uint32_dec_eq(v_curr_1601_, v___x_1604_);
if (v___x_1605_ == 0)
{
uint32_t v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = 32;
v___x_1607_ = lean_uint32_dec_eq(v_curr_1601_, v___x_1606_);
if (v___x_1607_ == 0)
{
if (v___x_1603_ == 0)
{
if (v___x_1605_ == 0)
{
uint32_t v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = 10;
v___x_1609_ = lean_uint32_dec_eq(v_curr_1601_, v___x_1608_);
if (v___x_1609_ == 0)
{
uint32_t v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = 45;
v___x_1611_ = lean_uint32_dec_eq(v_curr_1601_, v___x_1610_);
if (v___x_1611_ == 0)
{
uint32_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = 47;
v___x_1613_ = lean_uint32_dec_eq(v_curr_1601_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_dec_ref(v_c_1592_);
return v_s_1593_;
}
else
{
lean_object* v_i_1614_; uint32_t v_curr_1615_; uint8_t v___x_1616_; 
v_i_1614_ = lean_string_utf8_next_fast(v_inputString_1600_, v_pos_1594_);
v_curr_1615_ = lean_string_utf8_get(v_inputString_1600_, v_i_1614_);
v___x_1616_ = lean_uint32_dec_eq(v_curr_1615_, v___x_1610_);
if (v___x_1616_ == 0)
{
lean_dec_ref(v_c_1592_);
return v_s_1593_;
}
else
{
lean_object* v_i_1617_; uint32_t v_curr_1618_; uint8_t v___x_1619_; 
v_i_1617_ = lean_string_utf8_next(v_inputString_1600_, v_i_1614_);
v_curr_1618_ = lean_string_utf8_get(v_inputString_1600_, v_i_1617_);
v___x_1619_ = lean_uint32_dec_eq(v_curr_1618_, v___x_1610_);
if (v___x_1619_ == 0)
{
uint32_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 33;
v___x_1621_ = lean_uint32_dec_eq(v_curr_1618_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_box(v___x_1621_);
v___x_1624_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1624_, 0, v___x_1623_);
lean_closure_set(v___x_1624_, 1, v___x_1622_);
v___x_1625_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1626_ = l_Lean_Parser_ParserState_next(v_s_1593_, v_c_1592_, v_i_1617_);
lean_dec(v_i_1617_);
v___x_1627_ = l_Lean_Parser_andthenFn(v___x_1624_, v___x_1625_, v_c_1592_, v___x_1626_);
return v___x_1627_;
}
else
{
lean_dec(v_i_1617_);
lean_dec_ref(v_c_1592_);
return v_s_1593_;
}
}
else
{
lean_dec(v_i_1617_);
lean_dec_ref(v_c_1592_);
return v_s_1593_;
}
}
}
}
else
{
lean_object* v_i_1628_; uint32_t v_curr_1629_; uint8_t v___x_1630_; 
v_i_1628_ = lean_string_utf8_next_fast(v_inputString_1600_, v_pos_1594_);
v_curr_1629_ = lean_string_utf8_get(v_inputString_1600_, v_i_1628_);
v___x_1630_ = lean_uint32_dec_eq(v_curr_1629_, v___x_1610_);
if (v___x_1630_ == 0)
{
lean_dec_ref(v_c_1592_);
return v_s_1593_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1631_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1632_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1633_ = l_Lean_Parser_ParserState_next(v_s_1593_, v_c_1592_, v_i_1628_);
v___x_1634_ = l_Lean_Parser_andthenFn(v___x_1631_, v___x_1632_, v_c_1592_, v___x_1633_);
return v___x_1634_;
}
}
}
else
{
lean_inc(v_pos_1594_);
goto v___jp_1595_;
}
}
else
{
lean_inc(v_pos_1594_);
goto v___jp_1595_;
}
}
else
{
lean_inc(v_pos_1594_);
goto v___jp_1595_;
}
}
else
{
lean_inc(v_pos_1594_);
goto v___jp_1595_;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_c_1592_);
v___x_1635_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1593_, v___x_1635_, v___x_1636_, v___x_1603_);
return v___x_1637_;
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_c_1592_);
v___x_1638_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1593_, v___x_1638_, v___x_1639_, v___x_1599_);
return v___x_1640_;
}
}
else
{
lean_dec_ref(v_c_1592_);
return v_s_1593_;
}
v___jp_1595_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1593_, v_c_1592_, v_pos_1594_);
lean_dec(v_pos_1594_);
v_s_1593_ = v___x_1596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1641_, lean_object* v_p_1642_){
_start:
{
lean_object* v_toInputContext_1643_; lean_object* v_inputString_1644_; lean_object* v_endPos_1645_; uint8_t v___x_1646_; 
v_toInputContext_1643_ = lean_ctor_get(v_c_1641_, 0);
v_inputString_1644_ = lean_ctor_get(v_toInputContext_1643_, 0);
v_endPos_1645_ = lean_ctor_get(v_toInputContext_1643_, 3);
v___x_1646_ = lean_nat_dec_le(v_p_1642_, v_endPos_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_inc(v_endPos_1645_);
lean_inc_ref(v_inputString_1644_);
v___x_1647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1647_, 0, v_inputString_1644_);
lean_ctor_set(v___x_1647_, 1, v_p_1642_);
lean_ctor_set(v___x_1647_, 2, v_endPos_1645_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; 
lean_inc(v_p_1642_);
lean_inc_ref(v_inputString_1644_);
v___x_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1648_, 0, v_inputString_1644_);
lean_ctor_set(v___x_1648_, 1, v_p_1642_);
lean_ctor_set(v___x_1648_, 2, v_p_1642_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1649_, lean_object* v_p_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1649_, v_p_1650_);
lean_dec_ref(v_c_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1652_, uint8_t v_trailingWs_1653_, lean_object* v_c_1654_, lean_object* v_s_1655_){
_start:
{
lean_object* v_toInputContext_1656_; lean_object* v_pos_1657_; lean_object* v_inputString_1658_; lean_object* v_endPos_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1687_; 
v_toInputContext_1656_ = lean_ctor_get(v_c_1654_, 0);
lean_inc_ref(v_toInputContext_1656_);
v_pos_1657_ = lean_ctor_get(v_s_1655_, 2);
v_inputString_1658_ = lean_ctor_get(v_toInputContext_1656_, 0);
v_endPos_1659_ = lean_ctor_get(v_toInputContext_1656_, 3);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_toInputContext_1656_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; 
v_unused_1688_ = lean_ctor_get(v_toInputContext_1656_, 2);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_toInputContext_1656_, 1);
lean_dec(v_unused_1689_);
v___x_1661_ = v_toInputContext_1656_;
v_isShared_1662_ = v_isSharedCheck_1687_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_endPos_1659_);
lean_inc(v_inputString_1658_);
lean_dec(v_toInputContext_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1687_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v_leading_1663_; lean_object* v_val_1664_; 
lean_inc(v_startPos_1652_);
v_leading_1663_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1654_, v_startPos_1652_);
v_val_1664_ = lean_string_utf8_extract(v_inputString_1658_, v_startPos_1652_, v_pos_1657_);
if (v_trailingWs_1653_ == 0)
{
lean_object* v_trailing_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v_endPos_1659_);
lean_dec_ref(v_inputString_1658_);
lean_inc(v_pos_1657_);
v_trailing_1665_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1654_, v_pos_1657_);
lean_dec_ref(v_c_1654_);
v___x_1666_ = lean_string_utf8_byte_size(v_val_1664_);
v___x_1667_ = lean_nat_add(v_startPos_1652_, v___x_1666_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 3, v___x_1667_);
lean_ctor_set(v___x_1661_, 2, v_trailing_1665_);
lean_ctor_set(v___x_1661_, 1, v_startPos_1652_);
lean_ctor_set(v___x_1661_, 0, v_leading_1663_);
v___x_1669_ = v___x_1661_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_leading_1663_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_startPos_1652_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_trailing_1665_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v_atom_1670_; lean_object* v___x_1671_; 
v_atom_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1670_, 0, v___x_1669_);
lean_ctor_set(v_atom_1670_, 1, v_val_1664_);
v___x_1671_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1655_, v_atom_1670_);
return v___x_1671_;
}
}
else
{
lean_object* v_s_1673_; lean_object* v___y_1675_; lean_object* v_pos_1683_; uint8_t v___x_1684_; 
lean_inc(v_pos_1657_);
v_s_1673_ = l_Lean_Parser_whitespace(v_c_1654_, v_s_1655_);
v_pos_1683_ = lean_ctor_get(v_s_1673_, 2);
lean_inc(v_pos_1683_);
v___x_1684_ = lean_nat_dec_le(v_pos_1683_, v_endPos_1659_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_dec(v_pos_1683_);
v___x_1685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1685_, 0, v_inputString_1658_);
lean_ctor_set(v___x_1685_, 1, v_pos_1657_);
lean_ctor_set(v___x_1685_, 2, v_endPos_1659_);
v___y_1675_ = v___x_1685_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1686_; 
lean_dec(v_endPos_1659_);
v___x_1686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1686_, 0, v_inputString_1658_);
lean_ctor_set(v___x_1686_, 1, v_pos_1657_);
lean_ctor_set(v___x_1686_, 2, v_pos_1683_);
v___y_1675_ = v___x_1686_;
goto v___jp_1674_;
}
v___jp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1676_ = lean_string_utf8_byte_size(v_val_1664_);
v___x_1677_ = lean_nat_add(v_startPos_1652_, v___x_1676_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 3, v___x_1677_);
lean_ctor_set(v___x_1661_, 2, v___y_1675_);
lean_ctor_set(v___x_1661_, 1, v_startPos_1652_);
lean_ctor_set(v___x_1661_, 0, v_leading_1663_);
v___x_1679_ = v___x_1661_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_leading_1663_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_startPos_1652_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v___y_1675_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v_atom_1680_; lean_object* v___x_1681_; 
v_atom_1680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1680_, 0, v___x_1679_);
lean_ctor_set(v_atom_1680_, 1, v_val_1664_);
v___x_1681_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1673_, v_atom_1680_);
return v___x_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1690_, lean_object* v_trailingWs_1691_, lean_object* v_c_1692_, lean_object* v_s_1693_){
_start:
{
uint8_t v_trailingWs_boxed_1694_; lean_object* v_res_1695_; 
v_trailingWs_boxed_1694_ = lean_unbox(v_trailingWs_1691_);
v_res_1695_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1690_, v_trailingWs_boxed_1694_, v_c_1692_, v_s_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1696_, uint8_t v_trailingWs_1697_, lean_object* v_c_1698_, lean_object* v_s_1699_){
_start:
{
lean_object* v_pos_1700_; lean_object* v_s_1701_; lean_object* v_errorMsg_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_pos_1700_ = lean_ctor_get(v_s_1699_, 2);
lean_inc(v_pos_1700_);
lean_inc_ref(v_c_1698_);
v_s_1701_ = lean_apply_2(v_p_1696_, v_c_1698_, v_s_1699_);
v_errorMsg_1702_ = lean_ctor_get(v_s_1701_, 4);
lean_inc(v_errorMsg_1702_);
v___x_1703_ = lean_box(0);
v___x_1704_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1702_, v___x_1703_);
lean_dec(v_errorMsg_1702_);
if (v___x_1704_ == 0)
{
lean_dec(v_pos_1700_);
lean_dec_ref(v_c_1698_);
return v_s_1701_;
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1700_, v_trailingWs_1697_, v_c_1698_, v_s_1701_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1706_, lean_object* v_trailingWs_1707_, lean_object* v_c_1708_, lean_object* v_s_1709_){
_start:
{
uint8_t v_trailingWs_boxed_1710_; lean_object* v_res_1711_; 
v_trailingWs_boxed_1710_ = lean_unbox(v_trailingWs_1707_);
v_res_1711_ = l_Lean_Parser_rawFn(v_p_1706_, v_trailingWs_boxed_1710_, v_c_1708_, v_s_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1712_, uint32_t v_d_1713_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_uint32_dec_eq(v_c_1712_, v_d_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1715_, lean_object* v_d_1716_){
_start:
{
uint32_t v_c_boxed_1717_; uint32_t v_d_boxed_1718_; uint8_t v_res_1719_; lean_object* v_r_1720_; 
v_c_boxed_1717_ = lean_unbox_uint32(v_c_1715_);
lean_dec(v_c_1715_);
v_d_boxed_1718_ = lean_unbox_uint32(v_d_1716_);
lean_dec(v_d_1716_);
v_res_1719_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1717_, v_d_boxed_1718_);
v_r_1720_ = lean_box(v_res_1719_);
return v_r_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1723_, uint8_t v_trailingWs_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1727_ = lean_box_uint32(v_c_1723_);
v___f_1728_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1728_, 0, v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1730_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1731_ = lean_string_push(v___x_1730_, v_c_1723_);
v___x_1732_ = lean_string_append(v___x_1729_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = lean_string_append(v___x_1732_, v___x_1729_);
v___x_1734_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1734_, 0, v___f_1728_);
lean_closure_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Lean_Parser_rawFn(v___x_1734_, v_trailingWs_1724_, v_a_1725_, v_a_1726_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1736_, lean_object* v_trailingWs_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
uint32_t v_c_boxed_1740_; uint8_t v_trailingWs_boxed_1741_; lean_object* v_res_1742_; 
v_c_boxed_1740_ = lean_unbox_uint32(v_c_1736_);
lean_dec(v_c_1736_);
v_trailingWs_boxed_1741_ = lean_unbox(v_trailingWs_1737_);
v_res_1742_ = l_Lean_Parser_chFn(v_c_boxed_1740_, v_trailingWs_boxed_1741_, v_a_1738_, v_a_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1743_, uint8_t v_trailingWs_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1745_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1746_ = lean_box_uint32(v_c_1743_);
v___x_1747_ = lean_box(v_trailingWs_1744_);
v___x_1748_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1748_, 0, v___x_1746_);
lean_closure_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1745_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1750_, lean_object* v_trailingWs_1751_){
_start:
{
uint32_t v_c_boxed_1752_; uint8_t v_trailingWs_boxed_1753_; lean_object* v_res_1754_; 
v_c_boxed_1752_ = lean_unbox_uint32(v_c_1750_);
lean_dec(v_c_1750_);
v_trailingWs_boxed_1753_ = lean_unbox(v_trailingWs_1751_);
v_res_1754_ = l_Lean_Parser_rawCh(v_c_boxed_1752_, v_trailingWs_boxed_1753_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1756_, lean_object* v_s_1757_){
_start:
{
lean_object* v_pos_1758_; lean_object* v_toInputContext_1759_; uint8_t v___x_1760_; 
v_pos_1758_ = lean_ctor_get(v_s_1757_, 2);
v_toInputContext_1759_ = lean_ctor_get(v_c_1756_, 0);
v___x_1760_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1759_, v_pos_1758_);
if (v___x_1760_ == 0)
{
lean_object* v_inputString_1761_; uint8_t v___x_1762_; uint32_t v_curr_1763_; lean_object* v_i_1764_; uint8_t v___y_1766_; uint8_t v___y_1772_; uint32_t v___x_1783_; uint8_t v___x_1784_; 
v_inputString_1761_ = lean_ctor_get(v_toInputContext_1759_, 0);
v___x_1762_ = 1;
v_curr_1763_ = lean_string_utf8_get_fast(v_inputString_1761_, v_pos_1758_);
v_i_1764_ = lean_string_utf8_next_fast(v_inputString_1761_, v_pos_1758_);
v___x_1783_ = 48;
v___x_1784_ = lean_uint32_dec_le(v___x_1783_, v_curr_1763_);
if (v___x_1784_ == 0)
{
goto v___jp_1778_;
}
else
{
uint32_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = 57;
v___x_1786_ = lean_uint32_dec_le(v_curr_1763_, v___x_1785_);
if (v___x_1786_ == 0)
{
goto v___jp_1778_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Parser_ParserState_setPos(v_s_1757_, v_i_1764_);
return v___x_1787_;
}
}
v___jp_1765_:
{
if (v___y_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1757_, v___x_1767_, v___x_1768_, v___x_1762_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Parser_ParserState_setPos(v_s_1757_, v_i_1764_);
return v___x_1770_;
}
}
v___jp_1771_:
{
if (v___y_1772_ == 0)
{
uint32_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = 65;
v___x_1774_ = lean_uint32_dec_le(v___x_1773_, v_curr_1763_);
if (v___x_1774_ == 0)
{
v___y_1766_ = v___x_1760_;
goto v___jp_1765_;
}
else
{
uint32_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = 70;
v___x_1776_ = lean_uint32_dec_le(v_curr_1763_, v___x_1775_);
v___y_1766_ = v___x_1776_;
goto v___jp_1765_;
}
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Parser_ParserState_setPos(v_s_1757_, v_i_1764_);
return v___x_1777_;
}
}
v___jp_1778_:
{
uint32_t v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = 97;
v___x_1780_ = lean_uint32_dec_le(v___x_1779_, v_curr_1763_);
if (v___x_1780_ == 0)
{
v___y_1772_ = v___x_1760_;
goto v___jp_1771_;
}
else
{
uint32_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 102;
v___x_1782_ = lean_uint32_dec_le(v_curr_1763_, v___x_1781_);
v___y_1772_ = v___x_1782_;
goto v___jp_1771_;
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_box(0);
v___x_1789_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1757_, v___x_1788_);
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1790_, lean_object* v_s_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Parser_hexDigitFn(v_c_1790_, v_s_1791_);
lean_dec_ref(v_c_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1795_, lean_object* v_c_1796_, lean_object* v_s_1797_){
_start:
{
lean_object* v_pos_1798_; lean_object* v_toInputContext_1802_; uint8_t v___x_1803_; 
v_pos_1798_ = lean_ctor_get(v_s_1797_, 2);
v_toInputContext_1802_ = lean_ctor_get(v_c_1796_, 0);
v___x_1803_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1802_, v_pos_1798_);
if (v___x_1803_ == 0)
{
lean_object* v_inputString_1804_; uint8_t v___x_1805_; uint32_t v_curr_1806_; uint32_t v___x_1807_; uint8_t v___x_1808_; 
v_inputString_1804_ = lean_ctor_get(v_toInputContext_1802_, 0);
v___x_1805_ = 1;
v_curr_1806_ = lean_string_utf8_get_fast(v_inputString_1804_, v_pos_1798_);
v___x_1807_ = 10;
v___x_1808_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
uint32_t v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = 32;
v___x_1810_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1809_);
if (v___x_1810_ == 0)
{
uint32_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = 9;
v___x_1812_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1811_);
if (v___x_1812_ == 0)
{
uint32_t v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = 13;
v___x_1814_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1813_);
if (v___x_1814_ == 0)
{
if (v___x_1808_ == 0)
{
if (v_seenNewline_1795_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1816_ = lean_box(0);
v___x_1817_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1797_, v___x_1815_, v___x_1816_, v___x_1805_);
return v___x_1817_;
}
else
{
return v_s_1797_;
}
}
else
{
lean_inc(v_pos_1798_);
goto v___jp_1799_;
}
}
else
{
lean_inc(v_pos_1798_);
goto v___jp_1799_;
}
}
else
{
lean_inc(v_pos_1798_);
goto v___jp_1799_;
}
}
else
{
lean_inc(v_pos_1798_);
goto v___jp_1799_;
}
}
else
{
if (v_seenNewline_1795_ == 0)
{
lean_object* v___x_1818_; 
lean_inc(v_pos_1798_);
v___x_1818_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1797_, v_c_1796_, v_pos_1798_);
lean_dec(v_pos_1798_);
v_seenNewline_1795_ = v___x_1805_;
v_s_1797_ = v___x_1818_;
goto _start;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1821_ = lean_box(0);
v___x_1822_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1797_, v___x_1820_, v___x_1821_, v___x_1805_);
return v___x_1822_;
}
}
}
else
{
return v_s_1797_;
}
v___jp_1799_:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1797_, v_c_1796_, v_pos_1798_);
lean_dec(v_pos_1798_);
v_s_1797_ = v___x_1800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1823_, lean_object* v_c_1824_, lean_object* v_s_1825_){
_start:
{
uint8_t v_seenNewline_boxed_1826_; lean_object* v_res_1827_; 
v_seenNewline_boxed_1826_ = lean_unbox(v_seenNewline_1823_);
v_res_1827_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1826_, v_c_1824_, v_s_1825_);
lean_dec_ref(v_c_1824_);
return v_res_1827_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1829_);
v___x_1830_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1830_, 0, v___x_1829_);
lean_closure_set(v___x_1830_, 1, v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1832_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1833_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1833_, 0, v___x_1832_);
lean_closure_set(v___x_1833_, 1, v___x_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1834_, uint8_t v_inString_1835_, lean_object* v_c_1836_, lean_object* v_s_1837_){
_start:
{
lean_object* v_pos_1838_; lean_object* v_toInputContext_1839_; uint8_t v___x_1840_; 
v_pos_1838_ = lean_ctor_get(v_s_1837_, 2);
v_toInputContext_1839_ = lean_ctor_get(v_c_1836_, 0);
v___x_1840_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1839_, v_pos_1838_);
if (v___x_1840_ == 0)
{
lean_object* v_inputString_1841_; uint32_t v_curr_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_inputString_1841_ = lean_ctor_get(v_toInputContext_1839_, 0);
v_curr_1842_ = lean_string_utf8_get_fast(v_inputString_1841_, v_pos_1838_);
v___x_1843_ = lean_box_uint32(v_curr_1842_);
v___x_1844_ = lean_apply_1(v_isQuotable_1834_, v___x_1843_);
v___x_1845_ = lean_unbox(v___x_1844_);
if (v___x_1845_ == 0)
{
uint32_t v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = 120;
v___x_1847_ = lean_uint32_dec_eq(v_curr_1842_, v___x_1846_);
if (v___x_1847_ == 0)
{
uint32_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = 117;
v___x_1849_ = lean_uint32_dec_eq(v_curr_1842_, v___x_1848_);
if (v___x_1849_ == 0)
{
uint8_t v___x_1850_; 
v___x_1850_ = 1;
if (v_inString_1835_ == 0)
{
lean_dec_ref(v_c_1836_);
goto v___jp_1851_;
}
else
{
uint32_t v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = 10;
v___x_1856_ = lean_uint32_dec_eq(v_curr_1842_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_dec_ref(v_c_1836_);
goto v___jp_1851_;
}
else
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_Parser_stringGapFn(v___x_1849_, v_c_1836_, v_s_1837_);
lean_dec_ref(v_c_1836_);
return v___x_1857_;
}
}
v___jp_1851_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1853_ = lean_box(0);
v___x_1854_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1837_, v___x_1852_, v___x_1853_, v___x_1850_);
return v___x_1854_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_inc(v_pos_1838_);
v___x_1858_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1859_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1860_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1837_, v_c_1836_, v_pos_1838_);
lean_dec(v_pos_1838_);
v___x_1861_ = l_Lean_Parser_andthenFn(v___x_1858_, v___x_1859_, v_c_1836_, v___x_1860_);
return v___x_1861_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_inc(v_pos_1838_);
v___x_1862_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1863_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1837_, v_c_1836_, v_pos_1838_);
lean_dec(v_pos_1838_);
lean_inc_ref(v___x_1862_);
v___x_1864_ = l_Lean_Parser_andthenFn(v___x_1862_, v___x_1862_, v_c_1836_, v___x_1863_);
return v___x_1864_;
}
}
else
{
lean_object* v___x_1865_; 
lean_inc(v_pos_1838_);
v___x_1865_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1837_, v_c_1836_, v_pos_1838_);
lean_dec(v_pos_1838_);
lean_dec_ref(v_c_1836_);
return v___x_1865_;
}
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec_ref(v_c_1836_);
lean_dec_ref(v_isQuotable_1834_);
v___x_1866_ = lean_box(0);
v___x_1867_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1837_, v___x_1866_);
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1868_, lean_object* v_inString_1869_, lean_object* v_c_1870_, lean_object* v_s_1871_){
_start:
{
uint8_t v_inString_boxed_1872_; lean_object* v_res_1873_; 
v_inString_boxed_1872_ = lean_unbox(v_inString_1869_);
v_res_1873_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1868_, v_inString_boxed_1872_, v_c_1870_, v_s_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1874_){
_start:
{
uint32_t v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = 92;
v___x_1876_ = lean_uint32_dec_eq(v_c_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
uint32_t v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = 34;
v___x_1878_ = lean_uint32_dec_eq(v_c_1874_, v___x_1877_);
if (v___x_1878_ == 0)
{
uint32_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1879_ = 39;
v___x_1880_ = lean_uint32_dec_eq(v_c_1874_, v___x_1879_);
if (v___x_1880_ == 0)
{
uint32_t v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = 114;
v___x_1882_ = lean_uint32_dec_eq(v_c_1874_, v___x_1881_);
if (v___x_1882_ == 0)
{
uint32_t v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = 110;
v___x_1884_ = lean_uint32_dec_eq(v_c_1874_, v___x_1883_);
if (v___x_1884_ == 0)
{
uint32_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = 116;
v___x_1886_ = lean_uint32_dec_eq(v_c_1874_, v___x_1885_);
return v___x_1886_;
}
else
{
return v___x_1884_;
}
}
else
{
return v___x_1882_;
}
}
else
{
return v___x_1880_;
}
}
else
{
return v___x_1878_;
}
}
else
{
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1887_){
_start:
{
uint32_t v_c_boxed_1888_; uint8_t v_res_1889_; lean_object* v_r_1890_; 
v_c_boxed_1888_ = lean_unbox_uint32(v_c_1887_);
lean_dec(v_c_1887_);
v_res_1889_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1888_);
v_r_1890_ = lean_box(v_res_1889_);
return v_r_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1895_ = 0;
v___x_1896_ = l_Lean_Parser_quotedCharCoreFn(v___x_1894_, v___x_1895_, v_a_1892_, v_a_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1900_ = 1;
v___x_1901_ = l_Lean_Parser_quotedCharCoreFn(v___x_1899_, v___x_1900_, v_a_1897_, v_a_1898_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1902_, lean_object* v_startPos_1903_, uint8_t v_includeWhitespace_1904_, lean_object* v_c_1905_, lean_object* v_s_1906_){
_start:
{
lean_object* v_pos_1907_; lean_object* v_errorMsg_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_pos_1907_ = lean_ctor_get(v_s_1906_, 2);
v_errorMsg_1908_ = lean_ctor_get(v_s_1906_, 4);
v___x_1909_ = lean_box(0);
v___x_1910_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_dec_ref(v_c_1905_);
lean_dec(v_startPos_1903_);
lean_dec(v_n_1902_);
return v_s_1906_;
}
else
{
lean_object* v_toInputContext_1911_; lean_object* v_inputString_1912_; lean_object* v_endPos_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1935_; 
lean_inc(v_pos_1907_);
v_toInputContext_1911_ = lean_ctor_get(v_c_1905_, 0);
lean_inc_ref(v_toInputContext_1911_);
v_inputString_1912_ = lean_ctor_get(v_toInputContext_1911_, 0);
v_endPos_1913_ = lean_ctor_get(v_toInputContext_1911_, 3);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_toInputContext_1911_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; 
v_unused_1936_ = lean_ctor_get(v_toInputContext_1911_, 2);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_toInputContext_1911_, 1);
lean_dec(v_unused_1937_);
v___x_1915_ = v_toInputContext_1911_;
v_isShared_1916_ = v_isSharedCheck_1935_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_endPos_1913_);
lean_inc(v_inputString_1912_);
lean_dec(v_toInputContext_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1935_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_leading_1917_; lean_object* v_val_1918_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1928_; lean_object* v_pos_1929_; 
lean_inc(v_startPos_1903_);
v_leading_1917_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1905_, v_startPos_1903_);
v_val_1918_ = lean_string_utf8_extract(v_inputString_1912_, v_startPos_1903_, v_pos_1907_);
if (v_includeWhitespace_1904_ == 0)
{
lean_dec_ref(v_c_1905_);
lean_inc(v_pos_1907_);
v___y_1928_ = v_s_1906_;
v_pos_1929_ = v_pos_1907_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1933_; lean_object* v_pos_1934_; 
v___x_1933_ = l_Lean_Parser_whitespace(v_c_1905_, v_s_1906_);
v_pos_1934_ = lean_ctor_get(v___x_1933_, 2);
lean_inc(v_pos_1934_);
v___y_1928_ = v___x_1933_;
v_pos_1929_ = v_pos_1934_;
goto v___jp_1927_;
}
v___jp_1919_:
{
lean_object* v_info_1923_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 3, v_pos_1907_);
lean_ctor_set(v___x_1915_, 2, v___y_1921_);
lean_ctor_set(v___x_1915_, 1, v_startPos_1903_);
lean_ctor_set(v___x_1915_, 0, v_leading_1917_);
v_info_1923_ = v___x_1915_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_leading_1917_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_startPos_1903_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v___y_1921_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v_pos_1907_);
v_info_1923_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = l_Lean_Syntax_mkLit(v_n_1902_, v_val_1918_, v_info_1923_);
v___x_1925_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1920_, v___x_1924_);
return v___x_1925_;
}
}
v___jp_1927_:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_nat_dec_le(v_pos_1929_, v_endPos_1913_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec(v_pos_1929_);
lean_inc(v_pos_1907_);
v___x_1931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1931_, 0, v_inputString_1912_);
lean_ctor_set(v___x_1931_, 1, v_pos_1907_);
lean_ctor_set(v___x_1931_, 2, v_endPos_1913_);
v___y_1920_ = v___y_1928_;
v___y_1921_ = v___x_1931_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_endPos_1913_);
lean_inc(v_pos_1907_);
v___x_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1932_, 0, v_inputString_1912_);
lean_ctor_set(v___x_1932_, 1, v_pos_1907_);
lean_ctor_set(v___x_1932_, 2, v_pos_1929_);
v___y_1920_ = v___y_1928_;
v___y_1921_ = v___x_1932_;
goto v___jp_1919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1938_, lean_object* v_startPos_1939_, lean_object* v_includeWhitespace_1940_, lean_object* v_c_1941_, lean_object* v_s_1942_){
_start:
{
uint8_t v_includeWhitespace_boxed_1943_; lean_object* v_res_1944_; 
v_includeWhitespace_boxed_1943_ = lean_unbox(v_includeWhitespace_1940_);
v_res_1944_ = l_Lean_Parser_mkNodeToken(v_n_1938_, v_startPos_1939_, v_includeWhitespace_boxed_1943_, v_c_1941_, v_s_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1949_, lean_object* v_c_1950_, lean_object* v_s_1951_){
_start:
{
lean_object* v_pos_1952_; lean_object* v_toInputContext_1953_; uint8_t v___x_1954_; 
v_pos_1952_ = lean_ctor_get(v_s_1951_, 2);
v_toInputContext_1953_ = lean_ctor_get(v_c_1950_, 0);
v___x_1954_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1953_, v_pos_1952_);
if (v___x_1954_ == 0)
{
lean_object* v_inputString_1955_; uint8_t v___x_1956_; lean_object* v___y_1958_; uint32_t v_curr_1973_; lean_object* v___x_1974_; lean_object* v_s_1975_; uint32_t v___x_1976_; uint8_t v___x_1977_; 
v_inputString_1955_ = lean_ctor_get(v_toInputContext_1953_, 0);
v___x_1956_ = 1;
v_curr_1973_ = lean_string_utf8_get_fast(v_inputString_1955_, v_pos_1952_);
v___x_1974_ = lean_string_utf8_next_fast(v_inputString_1955_, v_pos_1952_);
v_s_1975_ = l_Lean_Parser_ParserState_setPos(v_s_1951_, v___x_1974_);
v___x_1976_ = 92;
v___x_1977_ = lean_uint32_dec_eq(v_curr_1973_, v___x_1976_);
if (v___x_1977_ == 0)
{
v___y_1958_ = v_s_1975_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_1978_; 
lean_inc_ref(v_c_1950_);
v___x_1978_ = l_Lean_Parser_quotedCharFn(v_c_1950_, v_s_1975_);
v___y_1958_ = v___x_1978_;
goto v___jp_1957_;
}
v___jp_1957_:
{
lean_object* v_pos_1959_; lean_object* v_errorMsg_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_pos_1959_ = lean_ctor_get(v___y_1958_, 2);
v_errorMsg_1960_ = lean_ctor_get(v___y_1958_, 4);
v___x_1961_ = lean_box(0);
v___x_1962_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1960_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec_ref(v_c_1950_);
lean_dec(v_startPos_1949_);
return v___y_1958_;
}
else
{
if (v___x_1954_ == 0)
{
uint32_t v_curr_1963_; lean_object* v___x_1964_; lean_object* v_s_1965_; uint32_t v___x_1966_; uint8_t v___x_1967_; 
v_curr_1963_ = lean_string_utf8_get(v_inputString_1955_, v_pos_1959_);
v___x_1964_ = lean_string_utf8_next(v_inputString_1955_, v_pos_1959_);
v_s_1965_ = l_Lean_Parser_ParserState_setPos(v___y_1958_, v___x_1964_);
v___x_1966_ = 39;
v___x_1967_ = lean_uint32_dec_eq(v_curr_1963_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec_ref(v_c_1950_);
lean_dec(v_startPos_1949_);
v___x_1968_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1969_ = lean_box(0);
v___x_1970_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1965_, v___x_1968_, v___x_1969_, v___x_1956_);
return v___x_1970_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1972_ = l_Lean_Parser_mkNodeToken(v___x_1971_, v_startPos_1949_, v___x_1956_, v_c_1950_, v_s_1965_);
return v___x_1972_;
}
}
else
{
lean_dec_ref(v_c_1950_);
lean_dec(v_startPos_1949_);
return v___y_1958_;
}
}
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_c_1950_);
lean_dec(v_startPos_1949_);
v___x_1979_ = lean_box(0);
v___x_1980_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1951_, v___x_1979_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_1985_, lean_object* v_includeWhitespace_1986_, lean_object* v_c_1987_, lean_object* v_s_1988_){
_start:
{
uint8_t v_includeWhitespace_boxed_1989_; lean_object* v_res_1990_; 
v_includeWhitespace_boxed_1989_ = lean_unbox(v_includeWhitespace_1986_);
v_res_1990_ = l_Lean_Parser_strLitFnAux(v_startPos_1985_, v_includeWhitespace_boxed_1989_, v_c_1987_, v_s_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_1991_, uint8_t v_includeWhitespace_1992_, lean_object* v_c_1993_, lean_object* v_s_1994_){
_start:
{
lean_object* v_pos_1995_; lean_object* v_toInputContext_1996_; uint8_t v___x_1997_; 
v_pos_1995_ = lean_ctor_get(v_s_1994_, 2);
v_toInputContext_1996_ = lean_ctor_get(v_c_1993_, 0);
v___x_1997_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1996_, v_pos_1995_);
if (v___x_1997_ == 0)
{
lean_object* v_inputString_1998_; uint32_t v_curr_1999_; lean_object* v___x_2000_; lean_object* v_s_2001_; uint32_t v___x_2002_; uint8_t v___x_2003_; 
v_inputString_1998_ = lean_ctor_get(v_toInputContext_1996_, 0);
v_curr_1999_ = lean_string_utf8_get_fast(v_inputString_1998_, v_pos_1995_);
v___x_2000_ = lean_string_utf8_next_fast(v_inputString_1998_, v_pos_1995_);
v_s_2001_ = l_Lean_Parser_ParserState_setPos(v_s_1994_, v___x_2000_);
v___x_2002_ = 34;
v___x_2003_ = lean_uint32_dec_eq(v_curr_1999_, v___x_2002_);
if (v___x_2003_ == 0)
{
uint32_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = 92;
v___x_2005_ = lean_uint32_dec_eq(v_curr_1999_, v___x_2004_);
if (v___x_2005_ == 0)
{
v_s_1994_ = v_s_2001_;
goto _start;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2007_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2008_ = lean_box(v___x_2005_);
v___x_2009_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2009_, 0, v_startPos_1991_);
lean_closure_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Lean_Parser_andthenFn(v___x_2007_, v___x_2009_, v_c_1993_, v_s_2001_);
return v___x_2010_;
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2012_ = l_Lean_Parser_mkNodeToken(v___x_2011_, v_startPos_1991_, v_includeWhitespace_1992_, v_c_1993_, v_s_2001_);
return v___x_2012_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v_c_1993_);
v___x_2013_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2014_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_1994_, v___x_2013_, v_startPos_1991_);
return v___x_2014_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2015_, lean_object* v_i_2016_){
_start:
{
lean_object* v_toInputContext_2017_; uint8_t v___x_2018_; 
v_toInputContext_2017_ = lean_ctor_get(v_c_2015_, 0);
v___x_2018_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2017_, v_i_2016_);
if (v___x_2018_ == 0)
{
lean_object* v_inputString_2019_; uint32_t v_curr_2020_; uint32_t v___x_2021_; uint8_t v___x_2022_; 
v_inputString_2019_ = lean_ctor_get(v_toInputContext_2017_, 0);
v_curr_2020_ = lean_string_utf8_get_fast(v_inputString_2019_, v_i_2016_);
v___x_2021_ = 35;
v___x_2022_ = lean_uint32_dec_eq(v_curr_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint32_t v___x_2023_; uint8_t v___x_2024_; 
lean_dec(v_i_2016_);
v___x_2023_ = 34;
v___x_2024_ = lean_uint32_dec_eq(v_curr_2020_, v___x_2023_);
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_string_utf8_next_fast(v_inputString_2019_, v_i_2016_);
lean_dec(v_i_2016_);
v_i_2016_ = v___x_2025_;
goto _start;
}
}
else
{
uint8_t v___x_2027_; 
lean_dec(v_i_2016_);
v___x_2027_ = 0;
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2028_, lean_object* v_i_2029_){
_start:
{
uint8_t v_res_2030_; lean_object* v_r_2031_; 
v_res_2030_ = l_Lean_Parser_isRawStrLitStart(v_c_2028_, v_i_2029_);
lean_dec_ref(v_c_2028_);
v_r_2031_ = lean_box(v_res_2030_);
return v_r_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2033_, lean_object* v_s_2034_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2036_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2034_, v___x_2035_, v_startPos_2033_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2037_, lean_object* v_num_2038_, lean_object* v_closingNum_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_pos_2042_; lean_object* v_toInputContext_2043_; uint8_t v___x_2044_; 
v_pos_2042_ = lean_ctor_get(v_a_2041_, 2);
v_toInputContext_2043_ = lean_ctor_get(v_a_2040_, 0);
v___x_2044_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2043_, v_pos_2042_);
if (v___x_2044_ == 0)
{
lean_object* v_inputString_2045_; uint32_t v_curr_2046_; lean_object* v___x_2047_; lean_object* v_s_2048_; uint32_t v___x_2049_; uint8_t v___x_2050_; 
v_inputString_2045_ = lean_ctor_get(v_toInputContext_2043_, 0);
v_curr_2046_ = lean_string_utf8_get_fast(v_inputString_2045_, v_pos_2042_);
v___x_2047_ = lean_string_utf8_next_fast(v_inputString_2045_, v_pos_2042_);
v_s_2048_ = l_Lean_Parser_ParserState_setPos(v_a_2041_, v___x_2047_);
v___x_2049_ = 35;
v___x_2050_ = lean_uint32_dec_eq(v_curr_2046_, v___x_2049_);
if (v___x_2050_ == 0)
{
uint32_t v___x_2051_; uint8_t v___x_2052_; 
lean_dec(v_closingNum_2039_);
v___x_2051_ = 34;
v___x_2052_ = lean_uint32_dec_eq(v_curr_2046_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2037_, v_num_2038_, v_a_2040_, v_s_2048_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_unsigned_to_nat(0u);
v_closingNum_2039_ = v___x_2054_;
v_a_2041_ = v_s_2048_;
goto _start;
}
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_add(v_closingNum_2039_, v___x_2056_);
lean_dec(v_closingNum_2039_);
v___x_2058_ = lean_nat_dec_eq(v___x_2057_, v_num_2038_);
if (v___x_2058_ == 0)
{
v_closingNum_2039_ = v___x_2057_;
v_a_2041_ = v_s_2048_;
goto _start;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec(v___x_2057_);
v___x_2060_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2061_ = l_Lean_Parser_mkNodeToken(v___x_2060_, v_startPos_2037_, v___x_2058_, v_a_2040_, v_s_2048_);
return v___x_2061_;
}
}
}
else
{
lean_object* v___x_2062_; 
lean_dec_ref(v_a_2040_);
lean_dec(v_closingNum_2039_);
v___x_2062_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2037_, v_a_2041_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2063_, lean_object* v_num_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_pos_2067_; lean_object* v_toInputContext_2068_; uint8_t v___x_2069_; 
v_pos_2067_ = lean_ctor_get(v_a_2066_, 2);
v_toInputContext_2068_ = lean_ctor_get(v_a_2065_, 0);
v___x_2069_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2068_, v_pos_2067_);
if (v___x_2069_ == 0)
{
lean_object* v_inputString_2070_; uint32_t v_curr_2071_; lean_object* v___x_2072_; lean_object* v_s_2073_; uint32_t v___x_2074_; uint8_t v___x_2075_; 
v_inputString_2070_ = lean_ctor_get(v_toInputContext_2068_, 0);
v_curr_2071_ = lean_string_utf8_get_fast(v_inputString_2070_, v_pos_2067_);
v___x_2072_ = lean_string_utf8_next_fast(v_inputString_2070_, v_pos_2067_);
v_s_2073_ = l_Lean_Parser_ParserState_setPos(v_a_2066_, v___x_2072_);
v___x_2074_ = 34;
v___x_2075_ = lean_uint32_dec_eq(v_curr_2071_, v___x_2074_);
if (v___x_2075_ == 0)
{
v_a_2066_ = v_s_2073_;
goto _start;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_nat_dec_eq(v_num_2064_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2063_, v_num_2064_, v___x_2077_, v_a_2065_, v_s_2073_);
return v___x_2079_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2081_ = l_Lean_Parser_mkNodeToken(v___x_2080_, v_startPos_2063_, v___x_2078_, v_a_2065_, v_s_2073_);
return v___x_2081_;
}
}
}
else
{
lean_object* v___x_2082_; 
lean_dec_ref(v_a_2065_);
v___x_2082_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2063_, v_a_2066_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2083_, lean_object* v_num_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2083_, v_num_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_num_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2088_, lean_object* v_num_2089_, lean_object* v_closingNum_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2088_, v_num_2089_, v_closingNum_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_num_2089_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2094_, lean_object* v_num_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_pos_2098_; lean_object* v_toInputContext_2099_; uint8_t v___x_2100_; 
v_pos_2098_ = lean_ctor_get(v_a_2097_, 2);
v_toInputContext_2099_ = lean_ctor_get(v_a_2096_, 0);
v___x_2100_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2099_, v_pos_2098_);
if (v___x_2100_ == 0)
{
lean_object* v_inputString_2101_; uint32_t v_curr_2102_; lean_object* v___x_2103_; lean_object* v_s_2104_; uint32_t v___x_2105_; uint8_t v___x_2106_; 
v_inputString_2101_ = lean_ctor_get(v_toInputContext_2099_, 0);
v_curr_2102_ = lean_string_utf8_get_fast(v_inputString_2101_, v_pos_2098_);
v___x_2103_ = lean_string_utf8_next_fast(v_inputString_2101_, v_pos_2098_);
v_s_2104_ = l_Lean_Parser_ParserState_setPos(v_a_2097_, v___x_2103_);
v___x_2105_ = 35;
v___x_2106_ = lean_uint32_dec_eq(v_curr_2102_, v___x_2105_);
if (v___x_2106_ == 0)
{
uint32_t v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = 34;
v___x_2108_ = lean_uint32_dec_eq(v_curr_2102_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec_ref(v_a_2096_);
lean_dec(v_num_2095_);
v___x_2109_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2094_, v_s_2104_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; 
v___x_2110_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2094_, v_num_2095_, v_a_2096_, v_s_2104_);
lean_dec(v_num_2095_);
return v___x_2110_;
}
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_nat_add(v_num_2095_, v___x_2111_);
lean_dec(v_num_2095_);
v_num_2095_ = v___x_2112_;
v_a_2097_ = v_s_2104_;
goto _start;
}
}
else
{
lean_object* v___x_2114_; 
lean_dec_ref(v_a_2096_);
lean_dec(v_num_2095_);
v___x_2114_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2094_, v_a_2097_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2115_, v___x_2118_, v_a_2116_, v_a_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2121_, lean_object* v_expecting_2122_, uint8_t v_needDigit_2123_, lean_object* v_c_2124_, lean_object* v_s_2125_){
_start:
{
lean_object* v_pos_2126_; lean_object* v_toInputContext_2127_; uint8_t v___x_2128_; 
v_pos_2126_ = lean_ctor_get(v_s_2125_, 2);
v_toInputContext_2127_ = lean_ctor_get(v_c_2124_, 0);
v___x_2128_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2127_, v_pos_2126_);
if (v___x_2128_ == 0)
{
lean_object* v_inputString_2129_; uint8_t v___x_2130_; uint32_t v_curr_2131_; uint32_t v___x_2132_; uint8_t v___x_2133_; 
v_inputString_2129_ = lean_ctor_get(v_toInputContext_2127_, 0);
v___x_2130_ = 1;
v_curr_2131_ = lean_string_utf8_get_fast(v_inputString_2129_, v_pos_2126_);
v___x_2132_ = 95;
v___x_2133_ = lean_uint32_dec_eq(v_curr_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2134_ = lean_box_uint32(v_curr_2131_);
lean_inc_ref(v_isDigit_2121_);
v___x_2135_ = lean_apply_1(v_isDigit_2121_, v___x_2134_);
v___x_2136_ = lean_unbox(v___x_2135_);
if (v___x_2136_ == 0)
{
lean_dec_ref(v_isDigit_2121_);
if (v_needDigit_2123_ == 0)
{
lean_dec_ref(v_expecting_2122_);
return v_s_2125_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_expecting_2122_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2125_, v___x_2137_, v___x_2139_, v___x_2130_);
return v___x_2140_;
}
}
else
{
lean_object* v___x_2141_; 
lean_inc(v_pos_2126_);
v___x_2141_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2125_, v_c_2124_, v_pos_2126_);
lean_dec(v_pos_2126_);
v_needDigit_2123_ = v___x_2133_;
v_s_2125_ = v___x_2141_;
goto _start;
}
}
else
{
lean_object* v___x_2143_; 
lean_inc(v_pos_2126_);
v___x_2143_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2125_, v_c_2124_, v_pos_2126_);
lean_dec(v_pos_2126_);
v_needDigit_2123_ = v___x_2130_;
v_s_2125_ = v___x_2143_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2121_);
if (v_needDigit_2123_ == 0)
{
lean_dec_ref(v_expecting_2122_);
return v_s_2125_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = lean_box(0);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_expecting_2122_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2125_, v___x_2146_);
return v___x_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2148_, lean_object* v_expecting_2149_, lean_object* v_needDigit_2150_, lean_object* v_c_2151_, lean_object* v_s_2152_){
_start:
{
uint8_t v_needDigit_boxed_2153_; lean_object* v_res_2154_; 
v_needDigit_boxed_2153_ = lean_unbox(v_needDigit_2150_);
v_res_2154_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2148_, v_expecting_2149_, v_needDigit_boxed_2153_, v_c_2151_, v_s_2152_);
lean_dec_ref(v_c_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2155_){
_start:
{
uint32_t v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = 48;
v___x_2157_ = lean_uint32_dec_le(v___x_2156_, v_c_2155_);
if (v___x_2157_ == 0)
{
return v___x_2157_;
}
else
{
uint32_t v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = 57;
v___x_2159_ = lean_uint32_dec_le(v_c_2155_, v___x_2158_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2160_){
_start:
{
uint32_t v_c_boxed_2161_; uint8_t v_res_2162_; lean_object* v_r_2163_; 
v_c_boxed_2161_ = lean_unbox_uint32(v_c_2160_);
lean_dec(v_c_2160_);
v_res_2162_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2161_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2168_, lean_object* v_c_2169_, lean_object* v_s_2170_, uint8_t v_hasBareDot_2171_){
_start:
{
lean_object* v_toInputContext_2172_; lean_object* v_pos_2173_; uint8_t v___x_2174_; 
v_toInputContext_2172_ = lean_ctor_get(v_c_2169_, 0);
v_pos_2173_ = lean_ctor_get(v_s_2170_, 2);
v___x_2174_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2172_, v_pos_2173_);
if (v___x_2174_ == 0)
{
lean_object* v_inputString_2175_; lean_object* v___f_2176_; uint8_t v___x_2177_; lean_object* v___y_2183_; lean_object* v___y_2193_; lean_object* v___y_2194_; uint32_t v_curr_2208_; uint8_t v___y_2216_; uint32_t v___x_2221_; uint8_t v___x_2222_; 
v_inputString_2175_ = lean_ctor_get(v_toInputContext_2172_, 0);
v___f_2176_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2177_ = 1;
v_curr_2208_ = lean_string_utf8_get_fast(v_inputString_2175_, v_pos_2173_);
v___x_2221_ = 101;
v___x_2222_ = lean_uint32_dec_eq(v_curr_2208_, v___x_2221_);
if (v___x_2222_ == 0)
{
uint32_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = 69;
v___x_2224_ = lean_uint32_dec_eq(v_curr_2208_, v___x_2223_);
if (v___x_2224_ == 0)
{
if (v_hasBareDot_2171_ == 0)
{
lean_dec(v_startPos_2168_);
return v_s_2170_;
}
else
{
uint32_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = 65;
v___x_2226_ = lean_uint32_dec_le(v___x_2225_, v_curr_2208_);
if (v___x_2226_ == 0)
{
v___y_2216_ = v___x_2226_;
goto v___jp_2215_;
}
else
{
uint32_t v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = 90;
v___x_2228_ = lean_uint32_dec_le(v_curr_2208_, v___x_2227_);
v___y_2216_ = v___x_2228_;
goto v___jp_2215_;
}
}
}
else
{
lean_dec(v_startPos_2168_);
goto v___jp_2196_;
}
}
else
{
lean_dec(v_startPos_2168_);
goto v___jp_2196_;
}
v___jp_2178_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2180_ = lean_box(0);
v___x_2181_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2170_, v___x_2179_, v___x_2180_, v___x_2177_);
return v___x_2181_;
}
v___jp_2182_:
{
uint32_t v_curr_2184_; uint32_t v___x_2185_; uint8_t v___x_2186_; 
v_curr_2184_ = lean_string_utf8_get(v_inputString_2175_, v___y_2183_);
v___x_2185_ = 48;
v___x_2186_ = lean_uint32_dec_le(v___x_2185_, v_curr_2184_);
if (v___x_2186_ == 0)
{
lean_dec(v___y_2183_);
goto v___jp_2178_;
}
else
{
uint32_t v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = 57;
v___x_2188_ = lean_uint32_dec_le(v_curr_2184_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_dec(v___y_2183_);
goto v___jp_2178_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2190_ = l_Lean_Parser_ParserState_setPos(v_s_2170_, v___y_2183_);
v___x_2191_ = l_Lean_Parser_takeDigitsFn(v___f_2176_, v___x_2189_, v___x_2174_, v_c_2169_, v___x_2190_);
return v___x_2191_;
}
}
}
v___jp_2192_:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_string_utf8_next(v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
v___y_2183_ = v___x_2195_;
goto v___jp_2182_;
}
v___jp_2196_:
{
lean_object* v_i_2197_; uint32_t v___x_2198_; uint32_t v___x_2199_; uint8_t v___x_2200_; 
v_i_2197_ = lean_string_utf8_next(v_inputString_2175_, v_pos_2173_);
v___x_2198_ = lean_string_utf8_get(v_inputString_2175_, v_i_2197_);
v___x_2199_ = 45;
v___x_2200_ = lean_uint32_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
uint32_t v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = 43;
v___x_2202_ = lean_uint32_dec_eq(v___x_2198_, v___x_2201_);
if (v___x_2202_ == 0)
{
v___y_2183_ = v_i_2197_;
goto v___jp_2182_;
}
else
{
v___y_2193_ = v_inputString_2175_;
v___y_2194_ = v_i_2197_;
goto v___jp_2192_;
}
}
else
{
v___y_2193_ = v_inputString_2175_;
v___y_2194_ = v_i_2197_;
goto v___jp_2192_;
}
}
v___jp_2203_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = l_Lean_Parser_ParserState_setPos(v_s_2170_, v_startPos_2168_);
v___x_2205_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2206_ = lean_box(0);
v___x_2207_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2204_, v___x_2205_, v___x_2206_, v___x_2177_);
return v___x_2207_;
}
v___jp_2209_:
{
uint32_t v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = 95;
v___x_2211_ = lean_uint32_dec_eq(v_curr_2208_, v___x_2210_);
if (v___x_2211_ == 0)
{
uint8_t v___x_2212_; 
v___x_2212_ = l_Lean_isLetterLike(v_curr_2208_);
if (v___x_2212_ == 0)
{
uint32_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = 171;
v___x_2214_ = lean_uint32_dec_eq(v_curr_2208_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_dec(v_startPos_2168_);
return v_s_2170_;
}
else
{
goto v___jp_2203_;
}
}
else
{
goto v___jp_2203_;
}
}
else
{
goto v___jp_2203_;
}
}
v___jp_2215_:
{
if (v___y_2216_ == 0)
{
uint32_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = 97;
v___x_2218_ = lean_uint32_dec_le(v___x_2217_, v_curr_2208_);
if (v___x_2218_ == 0)
{
goto v___jp_2209_;
}
else
{
uint32_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = 122;
v___x_2220_ = lean_uint32_dec_le(v_curr_2208_, v___x_2219_);
if (v___x_2220_ == 0)
{
goto v___jp_2209_;
}
else
{
goto v___jp_2203_;
}
}
}
else
{
goto v___jp_2203_;
}
}
}
else
{
lean_dec(v_startPos_2168_);
return v_s_2170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2229_, lean_object* v_c_2230_, lean_object* v_s_2231_, lean_object* v_hasBareDot_2232_){
_start:
{
uint8_t v_hasBareDot_boxed_2233_; lean_object* v_res_2234_; 
v_hasBareDot_boxed_2233_ = lean_unbox(v_hasBareDot_2232_);
v_res_2234_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2229_, v_c_2230_, v_s_2231_, v_hasBareDot_boxed_2233_);
lean_dec_ref(v_c_2230_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2235_, lean_object* v_s_2236_){
_start:
{
lean_object* v_toInputContext_2237_; lean_object* v_pos_2238_; lean_object* v_inputString_2239_; uint32_t v_curr_2240_; uint32_t v___x_2241_; uint8_t v___x_2242_; 
v_toInputContext_2237_ = lean_ctor_get(v_c_2235_, 0);
v_pos_2238_ = lean_ctor_get(v_s_2236_, 2);
v_inputString_2239_ = lean_ctor_get(v_toInputContext_2237_, 0);
v_curr_2240_ = lean_string_utf8_get(v_inputString_2239_, v_pos_2238_);
v___x_2241_ = 46;
v___x_2242_ = lean_uint32_dec_eq(v_curr_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_box(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_s_2236_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
return v___x_2244_;
}
else
{
lean_object* v_i_2245_; uint32_t v_curr_2250_; uint32_t v___x_2251_; uint8_t v___x_2252_; 
v_i_2245_ = lean_string_utf8_next(v_inputString_2239_, v_pos_2238_);
v_curr_2250_ = lean_string_utf8_get(v_inputString_2239_, v_i_2245_);
v___x_2251_ = 48;
v___x_2252_ = lean_uint32_dec_le(v___x_2251_, v_curr_2250_);
if (v___x_2252_ == 0)
{
goto v___jp_2246_;
}
else
{
uint32_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = 57;
v___x_2254_ = lean_uint32_dec_le(v_curr_2250_, v___x_2253_);
if (v___x_2254_ == 0)
{
goto v___jp_2246_;
}
else
{
lean_object* v___f_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___f_2255_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2256_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2257_ = 0;
v___x_2258_ = l_Lean_Parser_ParserState_setPos(v_s_2236_, v_i_2245_);
v___x_2259_ = l_Lean_Parser_takeDigitsFn(v___f_2255_, v___x_2256_, v___x_2257_, v_c_2235_, v___x_2258_);
v___x_2260_ = lean_box(v___x_2257_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
return v___x_2261_;
}
}
v___jp_2246_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = l_Lean_Parser_ParserState_setPos(v_s_2236_, v_i_2245_);
v___x_2248_ = lean_box(v___x_2242_);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
return v___x_2249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2262_, lean_object* v_s_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2262_, v_s_2263_);
lean_dec_ref(v_c_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2268_, uint8_t v_includeWhitespace_2269_, lean_object* v_c_2270_, lean_object* v_s_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v_fst_2273_; lean_object* v_snd_2274_; uint8_t v___x_2275_; lean_object* v_s_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2272_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2270_, v_s_2271_);
v_fst_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_fst_2273_);
v_snd_2274_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2274_);
lean_dec_ref(v___x_2272_);
v___x_2275_ = lean_unbox(v_snd_2274_);
lean_dec(v_snd_2274_);
lean_inc(v_startPos_2268_);
v_s_2276_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2268_, v_c_2270_, v_fst_2273_, v___x_2275_);
v___x_2277_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2278_ = l_Lean_Parser_mkNodeToken(v___x_2277_, v_startPos_2268_, v_includeWhitespace_2269_, v_c_2270_, v_s_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2279_, lean_object* v_includeWhitespace_2280_, lean_object* v_c_2281_, lean_object* v_s_2282_){
_start:
{
uint8_t v_includeWhitespace_boxed_2283_; lean_object* v_res_2284_; 
v_includeWhitespace_boxed_2283_ = lean_unbox(v_includeWhitespace_2280_);
v_res_2284_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2279_, v_includeWhitespace_boxed_2283_, v_c_2281_, v_s_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2288_, uint8_t v_includeWhitespace_2289_, lean_object* v_c_2290_, lean_object* v_s_2291_){
_start:
{
lean_object* v___f_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v_s_2295_; lean_object* v_pos_2296_; lean_object* v_toInputContext_2297_; uint8_t v___x_2298_; 
v___f_2292_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2293_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2294_ = 0;
v_s_2295_ = l_Lean_Parser_takeDigitsFn(v___f_2292_, v___x_2293_, v___x_2294_, v_c_2290_, v_s_2291_);
v_pos_2296_ = lean_ctor_get(v_s_2295_, 2);
lean_inc(v_pos_2296_);
v_toInputContext_2297_ = lean_ctor_get(v_c_2290_, 0);
v___x_2298_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2297_, v_pos_2296_);
if (v___x_2298_ == 0)
{
lean_object* v_inputString_2299_; uint32_t v_curr_2300_; lean_object* v_j_2313_; uint8_t v___x_2321_; 
v_inputString_2299_ = lean_ctor_get(v_toInputContext_2297_, 0);
v_curr_2300_ = lean_string_utf8_get_fast(v_inputString_2299_, v_pos_2296_);
v_j_2313_ = lean_string_utf8_next(v_inputString_2299_, v_pos_2296_);
lean_dec(v_pos_2296_);
v___x_2321_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2297_, v_j_2313_);
if (v___x_2321_ == 0)
{
goto v___jp_2314_;
}
else
{
if (v___x_2298_ == 0)
{
lean_dec(v_j_2313_);
goto v___jp_2301_;
}
else
{
goto v___jp_2314_;
}
}
v___jp_2301_:
{
uint32_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = 46;
v___x_2303_ = lean_uint32_dec_eq(v_curr_2300_, v___x_2302_);
if (v___x_2303_ == 0)
{
uint32_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = 101;
v___x_2305_ = lean_uint32_dec_eq(v_curr_2300_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint32_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = 69;
v___x_2307_ = lean_uint32_dec_eq(v_curr_2300_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2309_ = l_Lean_Parser_mkNodeToken(v___x_2308_, v_startPos_2288_, v_includeWhitespace_2289_, v_c_2290_, v_s_2295_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; 
v___x_2310_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2288_, v_includeWhitespace_2289_, v_c_2290_, v_s_2295_);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2311_; 
v___x_2311_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2288_, v_includeWhitespace_2289_, v_c_2290_, v_s_2295_);
return v___x_2311_;
}
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2288_, v_includeWhitespace_2289_, v_c_2290_, v_s_2295_);
return v___x_2312_;
}
}
v___jp_2314_:
{
uint32_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = 46;
v___x_2316_ = lean_uint32_dec_eq(v_curr_2300_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_dec(v_j_2313_);
goto v___jp_2301_;
}
else
{
uint32_t v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = lean_string_utf8_get_fast(v_inputString_2299_, v_j_2313_);
lean_dec(v_j_2313_);
v___x_2318_ = lean_uint32_dec_eq(v___x_2317_, v___x_2315_);
if (v___x_2318_ == 0)
{
goto v___jp_2301_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2320_ = l_Lean_Parser_mkNodeToken(v___x_2319_, v_startPos_2288_, v_includeWhitespace_2289_, v_c_2290_, v_s_2295_);
return v___x_2320_;
}
}
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_pos_2296_);
v___x_2322_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2323_ = l_Lean_Parser_mkNodeToken(v___x_2322_, v_startPos_2288_, v___x_2298_, v_c_2290_, v_s_2295_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2324_, lean_object* v_includeWhitespace_2325_, lean_object* v_c_2326_, lean_object* v_s_2327_){
_start:
{
uint8_t v_includeWhitespace_boxed_2328_; lean_object* v_res_2329_; 
v_includeWhitespace_boxed_2328_ = lean_unbox(v_includeWhitespace_2325_);
v_res_2329_ = l_Lean_Parser_decimalNumberFn(v_startPos_2324_, v_includeWhitespace_boxed_2328_, v_c_2326_, v_s_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2330_){
_start:
{
uint32_t v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = 48;
v___x_2332_ = lean_uint32_dec_eq(v_c_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
uint32_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = 49;
v___x_2334_ = lean_uint32_dec_eq(v_c_2330_, v___x_2333_);
return v___x_2334_;
}
else
{
return v___x_2332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2335_){
_start:
{
uint32_t v_c_boxed_2336_; uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_c_boxed_2336_ = lean_unbox_uint32(v_c_2335_);
lean_dec(v_c_2335_);
v_res_2337_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2336_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2341_, uint8_t v_includeWhitespace_2342_, lean_object* v_c_2343_, lean_object* v_s_2344_){
_start:
{
lean_object* v___f_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v_s_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___f_2345_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2346_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2347_ = 1;
v_s_2348_ = l_Lean_Parser_takeDigitsFn(v___f_2345_, v___x_2346_, v___x_2347_, v_c_2343_, v_s_2344_);
v___x_2349_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2350_ = l_Lean_Parser_mkNodeToken(v___x_2349_, v_startPos_2341_, v_includeWhitespace_2342_, v_c_2343_, v_s_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2351_, lean_object* v_includeWhitespace_2352_, lean_object* v_c_2353_, lean_object* v_s_2354_){
_start:
{
uint8_t v_includeWhitespace_boxed_2355_; lean_object* v_res_2356_; 
v_includeWhitespace_boxed_2355_ = lean_unbox(v_includeWhitespace_2352_);
v_res_2356_ = l_Lean_Parser_binNumberFn(v_startPos_2351_, v_includeWhitespace_boxed_2355_, v_c_2353_, v_s_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2357_){
_start:
{
uint32_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = 48;
v___x_2359_ = lean_uint32_dec_le(v___x_2358_, v_c_2357_);
if (v___x_2359_ == 0)
{
return v___x_2359_;
}
else
{
uint32_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = 55;
v___x_2361_ = lean_uint32_dec_le(v_c_2357_, v___x_2360_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2362_){
_start:
{
uint32_t v_c_boxed_2363_; uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_c_boxed_2363_ = lean_unbox_uint32(v_c_2362_);
lean_dec(v_c_2362_);
v_res_2364_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2363_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2368_, uint8_t v_includeWhitespace_2369_, lean_object* v_c_2370_, lean_object* v_s_2371_){
_start:
{
lean_object* v___f_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v_s_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___f_2372_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2373_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2374_ = 1;
v_s_2375_ = l_Lean_Parser_takeDigitsFn(v___f_2372_, v___x_2373_, v___x_2374_, v_c_2370_, v_s_2371_);
v___x_2376_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2377_ = l_Lean_Parser_mkNodeToken(v___x_2376_, v_startPos_2368_, v_includeWhitespace_2369_, v_c_2370_, v_s_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2378_, lean_object* v_includeWhitespace_2379_, lean_object* v_c_2380_, lean_object* v_s_2381_){
_start:
{
uint8_t v_includeWhitespace_boxed_2382_; lean_object* v_res_2383_; 
v_includeWhitespace_boxed_2382_ = lean_unbox(v_includeWhitespace_2379_);
v_res_2383_ = l_Lean_Parser_octalNumberFn(v_startPos_2378_, v_includeWhitespace_boxed_2382_, v_c_2380_, v_s_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2384_){
_start:
{
uint32_t v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = 48;
v___x_2396_ = lean_uint32_dec_le(v___x_2395_, v_c_2384_);
if (v___x_2396_ == 0)
{
goto v___jp_2390_;
}
else
{
uint32_t v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = 57;
v___x_2398_ = lean_uint32_dec_le(v_c_2384_, v___x_2397_);
if (v___x_2398_ == 0)
{
goto v___jp_2390_;
}
else
{
return v___x_2398_;
}
}
v___jp_2385_:
{
uint32_t v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = 65;
v___x_2387_ = lean_uint32_dec_le(v___x_2386_, v_c_2384_);
if (v___x_2387_ == 0)
{
return v___x_2387_;
}
else
{
uint32_t v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = 70;
v___x_2389_ = lean_uint32_dec_le(v_c_2384_, v___x_2388_);
return v___x_2389_;
}
}
v___jp_2390_:
{
uint32_t v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = 97;
v___x_2392_ = lean_uint32_dec_le(v___x_2391_, v_c_2384_);
if (v___x_2392_ == 0)
{
goto v___jp_2385_;
}
else
{
uint32_t v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = 102;
v___x_2394_ = lean_uint32_dec_le(v_c_2384_, v___x_2393_);
if (v___x_2394_ == 0)
{
goto v___jp_2385_;
}
else
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2399_){
_start:
{
uint32_t v_c_boxed_2400_; uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_c_boxed_2400_ = lean_unbox_uint32(v_c_2399_);
lean_dec(v_c_2399_);
v_res_2401_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2400_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2403_){
_start:
{
uint32_t v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = 48;
v___x_2415_ = lean_uint32_dec_le(v___x_2414_, v___y_2403_);
if (v___x_2415_ == 0)
{
goto v___jp_2409_;
}
else
{
uint32_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = 57;
v___x_2417_ = lean_uint32_dec_le(v___y_2403_, v___x_2416_);
if (v___x_2417_ == 0)
{
goto v___jp_2409_;
}
else
{
return v___x_2417_;
}
}
v___jp_2404_:
{
uint32_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = 65;
v___x_2406_ = lean_uint32_dec_le(v___x_2405_, v___y_2403_);
if (v___x_2406_ == 0)
{
return v___x_2406_;
}
else
{
uint32_t v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = 70;
v___x_2408_ = lean_uint32_dec_le(v___y_2403_, v___x_2407_);
return v___x_2408_;
}
}
v___jp_2409_:
{
uint32_t v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = 97;
v___x_2411_ = lean_uint32_dec_le(v___x_2410_, v___y_2403_);
if (v___x_2411_ == 0)
{
goto v___jp_2404_;
}
else
{
uint32_t v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = 102;
v___x_2413_ = lean_uint32_dec_le(v___y_2403_, v___x_2412_);
if (v___x_2413_ == 0)
{
goto v___jp_2404_;
}
else
{
return v___x_2413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2418_){
_start:
{
uint32_t v___y_104__boxed_2419_; uint8_t v_res_2420_; lean_object* v_r_2421_; 
v___y_104__boxed_2419_ = lean_unbox_uint32(v___y_2418_);
lean_dec(v___y_2418_);
v_res_2420_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_104__boxed_2419_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2424_, uint8_t v_includeWhitespace_2425_, lean_object* v_kind_2426_, lean_object* v_c_2427_, lean_object* v_s_2428_){
_start:
{
lean_object* v___f_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v_s_2432_; lean_object* v___x_2433_; 
v___f_2429_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2430_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2431_ = 1;
v_s_2432_ = l_Lean_Parser_takeDigitsFn(v___f_2429_, v___x_2430_, v___x_2431_, v_c_2427_, v_s_2428_);
v___x_2433_ = l_Lean_Parser_mkNodeToken(v_kind_2426_, v_startPos_2424_, v_includeWhitespace_2425_, v_c_2427_, v_s_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2434_, lean_object* v_includeWhitespace_2435_, lean_object* v_kind_2436_, lean_object* v_c_2437_, lean_object* v_s_2438_){
_start:
{
uint8_t v_includeWhitespace_boxed_2439_; lean_object* v_res_2440_; 
v_includeWhitespace_boxed_2439_ = lean_unbox(v_includeWhitespace_2435_);
v_res_2440_ = l_Lean_Parser_hexNumberFn(v_startPos_2434_, v_includeWhitespace_boxed_2439_, v_kind_2436_, v_c_2437_, v_s_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2442_, lean_object* v_c_2443_, lean_object* v_s_2444_){
_start:
{
lean_object* v_pos_2448_; lean_object* v_toInputContext_2449_; uint8_t v___x_2450_; 
v_pos_2448_ = lean_ctor_get(v_s_2444_, 2);
v_toInputContext_2449_ = lean_ctor_get(v_c_2443_, 0);
v___x_2450_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2449_, v_pos_2448_);
if (v___x_2450_ == 0)
{
lean_object* v_inputString_2451_; uint32_t v_curr_2452_; uint32_t v___x_2453_; uint8_t v___x_2454_; 
v_inputString_2451_ = lean_ctor_get(v_toInputContext_2449_, 0);
v_curr_2452_ = lean_string_utf8_get_fast(v_inputString_2451_, v_pos_2448_);
v___x_2453_ = 48;
v___x_2454_ = lean_uint32_dec_eq(v_curr_2452_, v___x_2453_);
if (v___x_2454_ == 0)
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_uint32_dec_le(v___x_2453_, v_curr_2452_);
if (v___x_2455_ == 0)
{
lean_dec_ref(v_c_2443_);
goto v___jp_2445_;
}
else
{
uint32_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = 57;
v___x_2457_ = lean_uint32_dec_le(v_curr_2452_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_dec_ref(v_c_2443_);
goto v___jp_2445_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_inc(v_pos_2448_);
v___x_2458_ = l_Lean_Parser_ParserState_next(v_s_2444_, v_c_2443_, v_pos_2448_);
v___x_2459_ = l_Lean_Parser_decimalNumberFn(v_pos_2448_, v_includeWhitespace_2442_, v_c_2443_, v___x_2458_);
return v___x_2459_;
}
}
}
else
{
lean_object* v_i_2460_; uint32_t v_curr_2471_; uint32_t v___x_2472_; uint8_t v___x_2473_; 
lean_inc(v_pos_2448_);
v_i_2460_ = lean_string_utf8_next_fast(v_inputString_2451_, v_pos_2448_);
v_curr_2471_ = lean_string_utf8_get(v_inputString_2451_, v_i_2460_);
v___x_2472_ = 98;
v___x_2473_ = lean_uint32_dec_eq(v_curr_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
uint32_t v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = 66;
v___x_2475_ = lean_uint32_dec_eq(v_curr_2471_, v___x_2474_);
if (v___x_2475_ == 0)
{
uint32_t v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = 111;
v___x_2477_ = lean_uint32_dec_eq(v_curr_2471_, v___x_2476_);
if (v___x_2477_ == 0)
{
uint32_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = 79;
v___x_2479_ = lean_uint32_dec_eq(v_curr_2471_, v___x_2478_);
if (v___x_2479_ == 0)
{
uint32_t v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = 120;
v___x_2481_ = lean_uint32_dec_eq(v_curr_2471_, v___x_2480_);
if (v___x_2481_ == 0)
{
uint32_t v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = 88;
v___x_2483_ = lean_uint32_dec_eq(v_curr_2471_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = l_Lean_Parser_ParserState_setPos(v_s_2444_, v_i_2460_);
v___x_2485_ = l_Lean_Parser_decimalNumberFn(v_pos_2448_, v_includeWhitespace_2442_, v_c_2443_, v___x_2484_);
return v___x_2485_;
}
else
{
goto v___jp_2461_;
}
}
else
{
goto v___jp_2461_;
}
}
else
{
goto v___jp_2465_;
}
}
else
{
goto v___jp_2465_;
}
}
else
{
goto v___jp_2468_;
}
}
else
{
goto v___jp_2468_;
}
v___jp_2461_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2463_ = l_Lean_Parser_ParserState_next(v_s_2444_, v_c_2443_, v_i_2460_);
v___x_2464_ = l_Lean_Parser_hexNumberFn(v_pos_2448_, v_includeWhitespace_2442_, v___x_2462_, v_c_2443_, v___x_2463_);
return v___x_2464_;
}
v___jp_2465_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = l_Lean_Parser_ParserState_next(v_s_2444_, v_c_2443_, v_i_2460_);
v___x_2467_ = l_Lean_Parser_octalNumberFn(v_pos_2448_, v_includeWhitespace_2442_, v_c_2443_, v___x_2466_);
return v___x_2467_;
}
v___jp_2468_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = l_Lean_Parser_ParserState_next(v_s_2444_, v_c_2443_, v_i_2460_);
v___x_2470_ = l_Lean_Parser_binNumberFn(v_pos_2448_, v_includeWhitespace_2442_, v_c_2443_, v___x_2469_);
return v___x_2470_;
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v_c_2443_);
v___x_2486_ = lean_box(0);
v___x_2487_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2444_, v___x_2486_);
return v___x_2487_;
}
v___jp_2445_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2447_ = l_Lean_Parser_ParserState_mkError(v_s_2444_, v___x_2446_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2488_, lean_object* v_c_2489_, lean_object* v_s_2490_){
_start:
{
uint8_t v_includeWhitespace_boxed_2491_; lean_object* v_res_2492_; 
v_includeWhitespace_boxed_2491_ = lean_unbox(v_includeWhitespace_2488_);
v_res_2492_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2491_, v_c_2489_, v_s_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2493_, lean_object* v_s_2494_){
_start:
{
lean_object* v_toInputContext_2495_; lean_object* v_pos_2496_; lean_object* v_inputString_2497_; uint32_t v_curr_2498_; uint32_t v___x_2499_; uint8_t v___x_2500_; 
v_toInputContext_2495_ = lean_ctor_get(v_c_2493_, 0);
v_pos_2496_ = lean_ctor_get(v_s_2494_, 2);
v_inputString_2497_ = lean_ctor_get(v_toInputContext_2495_, 0);
v_curr_2498_ = lean_string_utf8_get(v_inputString_2497_, v_pos_2496_);
v___x_2499_ = 46;
v___x_2500_ = lean_uint32_dec_eq(v_curr_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
return v___x_2500_;
}
else
{
lean_object* v_i_2501_; uint8_t v___x_2502_; 
v_i_2501_ = lean_string_utf8_next(v_inputString_2497_, v_pos_2496_);
v___x_2502_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2495_, v_i_2501_);
if (v___x_2502_ == 0)
{
uint32_t v_curr_2503_; uint8_t v___y_2511_; uint32_t v___x_2516_; uint8_t v___x_2517_; 
v_curr_2503_ = lean_string_utf8_get(v_inputString_2497_, v_i_2501_);
lean_dec(v_i_2501_);
v___x_2516_ = 65;
v___x_2517_ = lean_uint32_dec_le(v___x_2516_, v_curr_2503_);
if (v___x_2517_ == 0)
{
v___y_2511_ = v___x_2517_;
goto v___jp_2510_;
}
else
{
uint32_t v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = 90;
v___x_2519_ = lean_uint32_dec_le(v_curr_2503_, v___x_2518_);
v___y_2511_ = v___x_2519_;
goto v___jp_2510_;
}
v___jp_2504_:
{
uint32_t v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = 95;
v___x_2506_ = lean_uint32_dec_eq(v_curr_2503_, v___x_2505_);
if (v___x_2506_ == 0)
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Lean_isLetterLike(v_curr_2503_);
if (v___x_2507_ == 0)
{
uint32_t v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = 171;
v___x_2509_ = lean_uint32_dec_eq(v_curr_2503_, v___x_2508_);
return v___x_2509_;
}
else
{
return v___x_2500_;
}
}
else
{
return v___x_2500_;
}
}
v___jp_2510_:
{
if (v___y_2511_ == 0)
{
uint32_t v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = 97;
v___x_2513_ = lean_uint32_dec_le(v___x_2512_, v_curr_2503_);
if (v___x_2513_ == 0)
{
goto v___jp_2504_;
}
else
{
uint32_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = 122;
v___x_2515_ = lean_uint32_dec_le(v_curr_2503_, v___x_2514_);
if (v___x_2515_ == 0)
{
goto v___jp_2504_;
}
else
{
return v___x_2500_;
}
}
}
else
{
return v___x_2500_;
}
}
}
else
{
uint8_t v___x_2520_; 
lean_dec(v_i_2501_);
v___x_2520_ = 0;
return v___x_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2521_, lean_object* v_s_2522_){
_start:
{
uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_res_2523_ = l_Lean_Parser_isIdCont(v_c_2521_, v_s_2522_);
lean_dec_ref(v_s_2522_);
lean_dec_ref(v_c_2521_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2525_, lean_object* v_idStopPos_2526_, lean_object* v_tk_2527_){
_start:
{
if (lean_obj_tag(v_tk_2527_) == 0)
{
uint8_t v___x_2528_; 
v___x_2528_ = 0;
return v___x_2528_;
}
else
{
lean_object* v_val_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_val_2529_ = lean_ctor_get(v_tk_2527_, 0);
v___x_2530_ = lean_nat_sub(v_idStopPos_2526_, v_idStartPos_2525_);
v___x_2531_ = lean_string_utf8_byte_size(v_val_2529_);
v___x_2532_ = lean_nat_dec_le(v___x_2530_, v___x_2531_);
lean_dec(v___x_2530_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2533_, lean_object* v_idStopPos_2534_, lean_object* v_tk_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2533_, v_idStopPos_2534_, v_tk_2535_);
lean_dec(v_tk_2535_);
lean_dec(v_idStopPos_2534_);
lean_dec(v_idStartPos_2533_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object* v_a_2538_, lean_object* v_as_2539_, size_t v_i_2540_, size_t v_stop_2541_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_usize_dec_eq(v_i_2540_, v_stop_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = lean_array_uget_borrowed(v_as_2539_, v_i_2540_);
v___x_2544_ = lean_string_dec_eq(v_a_2538_, v___x_2543_);
if (v___x_2544_ == 0)
{
size_t v___x_2545_; size_t v___x_2546_; 
v___x_2545_ = ((size_t)1ULL);
v___x_2546_ = lean_usize_add(v_i_2540_, v___x_2545_);
v_i_2540_ = v___x_2546_;
goto _start;
}
else
{
return v___x_2544_;
}
}
else
{
uint8_t v___x_2548_; 
v___x_2548_ = 0;
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object* v_a_2549_, lean_object* v_as_2550_, lean_object* v_i_2551_, lean_object* v_stop_2552_){
_start:
{
size_t v_i_boxed_2553_; size_t v_stop_boxed_2554_; uint8_t v_res_2555_; lean_object* v_r_2556_; 
v_i_boxed_2553_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_stop_boxed_2554_ = lean_unbox_usize(v_stop_2552_);
lean_dec(v_stop_2552_);
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2549_, v_as_2550_, v_i_boxed_2553_, v_stop_boxed_2554_);
lean_dec_ref(v_as_2550_);
lean_dec_ref(v_a_2549_);
v_r_2556_ = lean_box(v_res_2555_);
return v_r_2556_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_as_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_array_get_size(v_as_2557_);
v___x_2561_ = lean_nat_dec_lt(v___x_2559_, v___x_2560_);
if (v___x_2561_ == 0)
{
return v___x_2561_;
}
else
{
if (v___x_2561_ == 0)
{
return v___x_2561_;
}
else
{
size_t v___x_2562_; size_t v___x_2563_; uint8_t v___x_2564_; 
v___x_2562_ = ((size_t)0ULL);
v___x_2563_ = lean_usize_of_nat(v___x_2560_);
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2558_, v_as_2557_, v___x_2562_, v___x_2563_);
return v___x_2564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_as_2565_, lean_object* v_a_2566_){
_start:
{
uint8_t v_res_2567_; lean_object* v_r_2568_; 
v_res_2567_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2565_, v_a_2566_);
lean_dec_ref(v_a_2566_);
lean_dec_ref(v_as_2565_);
v_r_2568_ = lean_box(v_res_2567_);
return v_r_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2571_, lean_object* v_tk_2572_, lean_object* v_c_2573_, lean_object* v_s_2574_){
_start:
{
if (lean_obj_tag(v_tk_2572_) == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v_c_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2576_ = lean_box(0);
v___x_2577_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2574_, v___x_2575_, v_startPos_2571_, v___x_2576_);
return v___x_2577_;
}
else
{
lean_object* v_toCacheableParserContext_2578_; lean_object* v_val_2579_; lean_object* v_toInputContext_2580_; lean_object* v_forbiddenTks_2581_; uint8_t v___x_2582_; 
v_toCacheableParserContext_2578_ = lean_ctor_get(v_c_2573_, 2);
v_val_2579_ = lean_ctor_get(v_tk_2572_, 0);
v_toInputContext_2580_ = lean_ctor_get(v_c_2573_, 0);
lean_inc_ref(v_toInputContext_2580_);
v_forbiddenTks_2581_ = lean_ctor_get(v_toCacheableParserContext_2578_, 3);
v___x_2582_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_2581_, v_val_2579_);
if (v___x_2582_ == 0)
{
lean_object* v_leading_2583_; lean_object* v___x_2584_; lean_object* v_stopPos_2585_; lean_object* v_s_2586_; lean_object* v_s_2587_; lean_object* v___y_2589_; lean_object* v_pos_2593_; lean_object* v_inputString_2594_; lean_object* v_endPos_2595_; uint8_t v___x_2596_; 
lean_inc(v_startPos_2571_);
v_leading_2583_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2573_, v_startPos_2571_);
v___x_2584_ = lean_string_utf8_byte_size(v_val_2579_);
v_stopPos_2585_ = lean_nat_add(v_startPos_2571_, v___x_2584_);
lean_inc(v_stopPos_2585_);
v_s_2586_ = l_Lean_Parser_ParserState_setPos(v_s_2574_, v_stopPos_2585_);
v_s_2587_ = l_Lean_Parser_whitespace(v_c_2573_, v_s_2586_);
v_pos_2593_ = lean_ctor_get(v_s_2587_, 2);
lean_inc(v_pos_2593_);
v_inputString_2594_ = lean_ctor_get(v_toInputContext_2580_, 0);
lean_inc_ref(v_inputString_2594_);
v_endPos_2595_ = lean_ctor_get(v_toInputContext_2580_, 3);
lean_inc(v_endPos_2595_);
lean_dec_ref(v_toInputContext_2580_);
v___x_2596_ = lean_nat_dec_le(v_pos_2593_, v_endPos_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
lean_dec(v_pos_2593_);
lean_inc(v_stopPos_2585_);
v___x_2597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2597_, 0, v_inputString_2594_);
lean_ctor_set(v___x_2597_, 1, v_stopPos_2585_);
lean_ctor_set(v___x_2597_, 2, v_endPos_2595_);
v___y_2589_ = v___x_2597_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2598_; 
lean_dec(v_endPos_2595_);
lean_inc(v_stopPos_2585_);
v___x_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2598_, 0, v_inputString_2594_);
lean_ctor_set(v___x_2598_, 1, v_stopPos_2585_);
lean_ctor_set(v___x_2598_, 2, v_pos_2593_);
v___y_2589_ = v___x_2598_;
goto v___jp_2588_;
}
v___jp_2588_:
{
lean_object* v___x_2590_; lean_object* v_atom_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2590_, 0, v_leading_2583_);
lean_ctor_set(v___x_2590_, 1, v_startPos_2571_);
lean_ctor_set(v___x_2590_, 2, v___y_2589_);
lean_ctor_set(v___x_2590_, 3, v_stopPos_2585_);
lean_inc(v_val_2579_);
v_atom_2591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2591_, 0, v___x_2590_);
lean_ctor_set(v_atom_2591_, 1, v_val_2579_);
v___x_2592_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2587_, v_atom_2591_);
return v___x_2592_;
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_toInputContext_2580_);
lean_dec_ref(v_c_2573_);
v___x_2599_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2574_, v___x_2599_, v_startPos_2571_, v___x_2600_);
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2602_, lean_object* v_tk_2603_, lean_object* v_c_2604_, lean_object* v_s_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2602_, v_tk_2603_, v_c_2604_, v_s_2605_);
lean_dec(v_tk_2603_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2607_, lean_object* v_tk_2608_, lean_object* v_val_2609_, uint8_t v_includeWhitespace_2610_, lean_object* v_c_2611_, lean_object* v_s_2612_){
_start:
{
lean_object* v_pos_2613_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; uint8_t v___x_2623_; 
v_pos_2613_ = lean_ctor_get(v_s_2612_, 2);
v___x_2623_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2607_, v_pos_2613_, v_tk_2608_);
if (v___x_2623_ == 0)
{
lean_object* v_toInputContext_2624_; lean_object* v_inputString_2625_; lean_object* v_endPos_2626_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v_pos_2630_; lean_object* v___y_2636_; uint8_t v___x_2639_; 
lean_inc(v_pos_2613_);
v_toInputContext_2624_ = lean_ctor_get(v_c_2611_, 0);
v_inputString_2625_ = lean_ctor_get(v_toInputContext_2624_, 0);
lean_inc_ref(v_inputString_2625_);
v_endPos_2626_ = lean_ctor_get(v_toInputContext_2624_, 3);
lean_inc(v_endPos_2626_);
v___x_2639_ = lean_nat_dec_le(v_pos_2613_, v_endPos_2626_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
lean_inc(v_endPos_2626_);
lean_inc(v_startPos_2607_);
lean_inc_ref(v_inputString_2625_);
v___x_2640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2640_, 0, v_inputString_2625_);
lean_ctor_set(v___x_2640_, 1, v_startPos_2607_);
lean_ctor_set(v___x_2640_, 2, v_endPos_2626_);
v___y_2636_ = v___x_2640_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2641_; 
lean_inc(v_pos_2613_);
lean_inc(v_startPos_2607_);
lean_inc_ref(v_inputString_2625_);
v___x_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2641_, 0, v_inputString_2625_);
lean_ctor_set(v___x_2641_, 1, v_startPos_2607_);
lean_ctor_set(v___x_2641_, 2, v_pos_2613_);
v___y_2636_ = v___x_2641_;
goto v___jp_2635_;
}
v___jp_2627_:
{
lean_object* v_leading_2631_; uint8_t v___x_2632_; 
lean_inc(v_startPos_2607_);
v_leading_2631_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2611_, v_startPos_2607_);
lean_dec_ref(v_c_2611_);
v___x_2632_ = lean_nat_dec_le(v_pos_2630_, v_endPos_2626_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec(v_pos_2630_);
lean_inc(v_pos_2613_);
v___x_2633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2633_, 0, v_inputString_2625_);
lean_ctor_set(v___x_2633_, 1, v_pos_2613_);
lean_ctor_set(v___x_2633_, 2, v_endPos_2626_);
v___y_2615_ = v___y_2628_;
v___y_2616_ = v___y_2629_;
v___y_2617_ = v_leading_2631_;
v___y_2618_ = v___x_2633_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2634_; 
lean_dec(v_endPos_2626_);
lean_inc(v_pos_2613_);
v___x_2634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2634_, 0, v_inputString_2625_);
lean_ctor_set(v___x_2634_, 1, v_pos_2613_);
lean_ctor_set(v___x_2634_, 2, v_pos_2630_);
v___y_2615_ = v___y_2628_;
v___y_2616_ = v___y_2629_;
v___y_2617_ = v_leading_2631_;
v___y_2618_ = v___x_2634_;
goto v___jp_2614_;
}
}
v___jp_2635_:
{
if (v_includeWhitespace_2610_ == 0)
{
lean_inc(v_pos_2613_);
v___y_2628_ = v___y_2636_;
v___y_2629_ = v_s_2612_;
v_pos_2630_ = v_pos_2613_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2637_; lean_object* v_pos_2638_; 
lean_inc_ref(v_c_2611_);
v___x_2637_ = l_Lean_Parser_whitespace(v_c_2611_, v_s_2612_);
v_pos_2638_ = lean_ctor_get(v___x_2637_, 2);
lean_inc(v_pos_2638_);
v___y_2628_ = v___y_2636_;
v___y_2629_ = v___x_2637_;
v_pos_2630_ = v_pos_2638_;
goto v___jp_2627_;
}
}
}
else
{
lean_object* v___x_2642_; 
lean_dec(v_val_2609_);
v___x_2642_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2607_, v_tk_2608_, v_c_2611_, v_s_2612_);
return v___x_2642_;
}
v___jp_2614_:
{
lean_object* v_info_2619_; lean_object* v___x_2620_; lean_object* v_atom_2621_; lean_object* v___x_2622_; 
v_info_2619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2619_, 0, v___y_2617_);
lean_ctor_set(v_info_2619_, 1, v_startPos_2607_);
lean_ctor_set(v_info_2619_, 2, v___y_2618_);
lean_ctor_set(v_info_2619_, 3, v_pos_2613_);
v___x_2620_ = lean_box(0);
v_atom_2621_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2621_, 0, v_info_2619_);
lean_ctor_set(v_atom_2621_, 1, v___y_2615_);
lean_ctor_set(v_atom_2621_, 2, v_val_2609_);
lean_ctor_set(v_atom_2621_, 3, v___x_2620_);
v___x_2622_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2616_, v_atom_2621_);
return v___x_2622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2643_, lean_object* v_tk_2644_, lean_object* v_val_2645_, lean_object* v_includeWhitespace_2646_, lean_object* v_c_2647_, lean_object* v_s_2648_){
_start:
{
uint8_t v_includeWhitespace_boxed_2649_; lean_object* v_res_2650_; 
v_includeWhitespace_boxed_2649_ = lean_unbox(v_includeWhitespace_2646_);
v_res_2650_ = l_Lean_Parser_mkIdResult(v_startPos_2643_, v_tk_2644_, v_val_2645_, v_includeWhitespace_boxed_2649_, v_c_2647_, v_s_2648_);
lean_dec(v_tk_2644_);
return v_res_2650_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2651_){
_start:
{
uint8_t v___y_2669_; uint32_t v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = 65;
v___x_2675_ = lean_uint32_dec_le(v___x_2674_, v___y_2651_);
if (v___x_2675_ == 0)
{
v___y_2669_ = v___x_2675_;
goto v___jp_2668_;
}
else
{
uint32_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = 90;
v___x_2677_ = lean_uint32_dec_le(v___y_2651_, v___x_2676_);
v___y_2669_ = v___x_2677_;
goto v___jp_2668_;
}
v___jp_2652_:
{
uint32_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = 95;
v___x_2654_ = lean_uint32_dec_eq(v___y_2651_, v___x_2653_);
if (v___x_2654_ == 0)
{
uint32_t v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = 39;
v___x_2656_ = lean_uint32_dec_eq(v___y_2651_, v___x_2655_);
if (v___x_2656_ == 0)
{
uint32_t v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = 33;
v___x_2658_ = lean_uint32_dec_eq(v___y_2651_, v___x_2657_);
if (v___x_2658_ == 0)
{
uint32_t v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = 63;
v___x_2660_ = lean_uint32_dec_eq(v___y_2651_, v___x_2659_);
if (v___x_2660_ == 0)
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_isLetterLike(v___y_2651_);
if (v___x_2661_ == 0)
{
uint8_t v___x_2662_; 
v___x_2662_ = l_Lean_isSubScriptAlnum(v___y_2651_);
return v___x_2662_;
}
else
{
return v___x_2661_;
}
}
else
{
return v___x_2660_;
}
}
else
{
return v___x_2658_;
}
}
else
{
return v___x_2656_;
}
}
else
{
return v___x_2654_;
}
}
v___jp_2663_:
{
uint32_t v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = 48;
v___x_2665_ = lean_uint32_dec_le(v___x_2664_, v___y_2651_);
if (v___x_2665_ == 0)
{
goto v___jp_2652_;
}
else
{
uint32_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = 57;
v___x_2667_ = lean_uint32_dec_le(v___y_2651_, v___x_2666_);
if (v___x_2667_ == 0)
{
goto v___jp_2652_;
}
else
{
return v___x_2667_;
}
}
}
v___jp_2668_:
{
if (v___y_2669_ == 0)
{
uint32_t v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = 97;
v___x_2671_ = lean_uint32_dec_le(v___x_2670_, v___y_2651_);
if (v___x_2671_ == 0)
{
goto v___jp_2663_;
}
else
{
uint32_t v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = 122;
v___x_2673_ = lean_uint32_dec_le(v___y_2651_, v___x_2672_);
if (v___x_2673_ == 0)
{
goto v___jp_2663_;
}
else
{
return v___x_2673_;
}
}
}
else
{
return v___y_2669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2678_){
_start:
{
uint32_t v___y_295__boxed_2679_; uint8_t v_res_2680_; lean_object* v_r_2681_; 
v___y_295__boxed_2679_ = lean_unbox_uint32(v___y_2678_);
lean_dec(v___y_2678_);
v_res_2680_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_295__boxed_2679_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2682_){
_start:
{
uint32_t v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = 187;
v___x_2684_ = lean_uint32_dec_eq(v___y_2682_, v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2685_){
_start:
{
uint32_t v___y_350__boxed_2686_; uint8_t v_res_2687_; lean_object* v_r_2688_; 
v___y_350__boxed_2686_ = lean_unbox_uint32(v___y_2685_);
lean_dec(v___y_2685_);
v_res_2687_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_350__boxed_2686_);
v_r_2688_ = lean_box(v_res_2687_);
return v_r_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2692_, lean_object* v_tk_2693_, uint8_t v_includeWhitespace_2694_, lean_object* v_r_2695_, lean_object* v_c_2696_, lean_object* v_s_2697_){
_start:
{
lean_object* v_pos_2698_; lean_object* v_toInputContext_2699_; uint8_t v___x_2700_; 
v_pos_2698_ = lean_ctor_get(v_s_2697_, 2);
v_toInputContext_2699_ = lean_ctor_get(v_c_2696_, 0);
v___x_2700_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2699_, v_pos_2698_);
if (v___x_2700_ == 0)
{
lean_object* v_inputString_2701_; uint32_t v_curr_2702_; uint32_t v___x_2703_; uint8_t v___x_2704_; 
v_inputString_2701_ = lean_ctor_get(v_toInputContext_2699_, 0);
v_curr_2702_ = lean_string_utf8_get_fast(v_inputString_2701_, v_pos_2698_);
v___x_2703_ = 171;
v___x_2704_ = lean_uint32_dec_eq(v_curr_2702_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___f_2705_; uint8_t v___y_2722_; uint32_t v___x_2727_; uint8_t v___x_2728_; 
v___f_2705_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2727_ = 65;
v___x_2728_ = lean_uint32_dec_le(v___x_2727_, v_curr_2702_);
if (v___x_2728_ == 0)
{
v___y_2722_ = v___x_2728_;
goto v___jp_2721_;
}
else
{
uint32_t v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = 90;
v___x_2730_ = lean_uint32_dec_le(v_curr_2702_, v___x_2729_);
v___y_2722_ = v___x_2730_;
goto v___jp_2721_;
}
v___jp_2706_:
{
lean_object* v___x_2707_; lean_object* v_s_2708_; lean_object* v_pos_2709_; lean_object* v___x_2710_; lean_object* v_r_2711_; uint8_t v___x_2712_; 
v___x_2707_ = l_Lean_Parser_ParserState_next(v_s_2697_, v_c_2696_, v_pos_2698_);
v_s_2708_ = l_Lean_Parser_takeWhileFn(v___f_2705_, v_c_2696_, v___x_2707_);
v_pos_2709_ = lean_ctor_get(v_s_2708_, 2);
lean_inc(v_pos_2709_);
v___x_2710_ = lean_string_utf8_extract(v_inputString_2701_, v_pos_2698_, v_pos_2709_);
lean_dec(v_pos_2698_);
v_r_2711_ = l_Lean_Name_str___override(v_r_2695_, v___x_2710_);
v___x_2712_ = l_Lean_Parser_isIdCont(v_c_2696_, v_s_2708_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; 
lean_dec(v_pos_2709_);
v___x_2713_ = l_Lean_Parser_mkIdResult(v_startPos_2692_, v_tk_2693_, v_r_2711_, v_includeWhitespace_2694_, v_c_2696_, v_s_2708_);
return v___x_2713_;
}
else
{
lean_object* v_s_2714_; 
v_s_2714_ = l_Lean_Parser_ParserState_next(v_s_2708_, v_c_2696_, v_pos_2709_);
lean_dec(v_pos_2709_);
v_r_2695_ = v_r_2711_;
v_s_2697_ = v_s_2714_;
goto _start;
}
}
v___jp_2716_:
{
uint32_t v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = 95;
v___x_2718_ = lean_uint32_dec_eq(v_curr_2702_, v___x_2717_);
if (v___x_2718_ == 0)
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Lean_isLetterLike(v_curr_2702_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_dec(v_r_2695_);
v___x_2720_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2692_, v_tk_2693_, v_c_2696_, v_s_2697_);
return v___x_2720_;
}
else
{
lean_inc(v_pos_2698_);
goto v___jp_2706_;
}
}
else
{
lean_inc(v_pos_2698_);
goto v___jp_2706_;
}
}
v___jp_2721_:
{
if (v___y_2722_ == 0)
{
uint32_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = 97;
v___x_2724_ = lean_uint32_dec_le(v___x_2723_, v_curr_2702_);
if (v___x_2724_ == 0)
{
goto v___jp_2716_;
}
else
{
uint32_t v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = 122;
v___x_2726_ = lean_uint32_dec_le(v_curr_2702_, v___x_2725_);
if (v___x_2726_ == 0)
{
goto v___jp_2716_;
}
else
{
lean_inc(v_pos_2698_);
goto v___jp_2706_;
}
}
}
else
{
lean_inc(v_pos_2698_);
goto v___jp_2706_;
}
}
}
else
{
lean_object* v___f_2731_; lean_object* v_startPart_2732_; lean_object* v___x_2733_; lean_object* v_s_2734_; lean_object* v_pos_2735_; uint8_t v___x_2736_; 
v___f_2731_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2732_ = lean_string_utf8_next_fast(v_inputString_2701_, v_pos_2698_);
v___x_2733_ = l_Lean_Parser_ParserState_setPos(v_s_2697_, v_startPart_2732_);
v_s_2734_ = l_Lean_Parser_takeUntilFn(v___f_2731_, v_c_2696_, v___x_2733_);
v_pos_2735_ = lean_ctor_get(v_s_2734_, 2);
lean_inc(v_pos_2735_);
v___x_2736_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2699_, v_pos_2735_);
if (v___x_2736_ == 0)
{
lean_object* v_s_2737_; lean_object* v___x_2738_; lean_object* v_r_2739_; uint8_t v___x_2740_; 
v_s_2737_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2734_, v_c_2696_, v_pos_2735_);
v___x_2738_ = lean_string_utf8_extract(v_inputString_2701_, v_startPart_2732_, v_pos_2735_);
lean_dec(v_pos_2735_);
v_r_2739_ = l_Lean_Name_str___override(v_r_2695_, v___x_2738_);
v___x_2740_ = l_Lean_Parser_isIdCont(v_c_2696_, v_s_2737_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Parser_mkIdResult(v_startPos_2692_, v_tk_2693_, v_r_2739_, v_includeWhitespace_2694_, v_c_2696_, v_s_2737_);
return v___x_2741_;
}
else
{
lean_object* v_pos_2742_; lean_object* v_s_2743_; 
v_pos_2742_ = lean_ctor_get(v_s_2737_, 2);
lean_inc(v_pos_2742_);
v_s_2743_ = l_Lean_Parser_ParserState_next(v_s_2737_, v_c_2696_, v_pos_2742_);
lean_dec(v_pos_2742_);
v_r_2695_ = v_r_2739_;
v_s_2697_ = v_s_2743_;
goto _start;
}
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v_pos_2735_);
lean_dec_ref(v_c_2696_);
lean_dec(v_r_2695_);
lean_dec(v_startPos_2692_);
v___x_2745_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2746_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2734_, v___x_2745_, v_startPart_2732_);
return v___x_2746_;
}
}
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec_ref(v_c_2696_);
lean_dec(v_r_2695_);
lean_dec(v_startPos_2692_);
v___x_2747_ = lean_box(0);
v___x_2748_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2697_, v___x_2747_);
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2749_, lean_object* v_tk_2750_, lean_object* v_includeWhitespace_2751_, lean_object* v_r_2752_, lean_object* v_c_2753_, lean_object* v_s_2754_){
_start:
{
uint8_t v_includeWhitespace_boxed_2755_; lean_object* v_res_2756_; 
v_includeWhitespace_boxed_2755_ = lean_unbox(v_includeWhitespace_2751_);
v_res_2756_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2749_, v_tk_2750_, v_includeWhitespace_boxed_2755_, v_r_2752_, v_c_2753_, v_s_2754_);
lean_dec(v_tk_2750_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2757_, lean_object* v_tk_2758_, lean_object* v_r_2759_, uint8_t v_includeWhitespace_2760_, lean_object* v_c_2761_, lean_object* v_s_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2757_, v_tk_2758_, v_includeWhitespace_2760_, v_r_2759_, v_c_2761_, v_s_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2764_, lean_object* v_tk_2765_, lean_object* v_r_2766_, lean_object* v_includeWhitespace_2767_, lean_object* v_c_2768_, lean_object* v_s_2769_){
_start:
{
uint8_t v_includeWhitespace_boxed_2770_; lean_object* v_res_2771_; 
v_includeWhitespace_boxed_2770_ = lean_unbox(v_includeWhitespace_2767_);
v_res_2771_ = l_Lean_Parser_identFnAux(v_startPos_2764_, v_tk_2765_, v_r_2766_, v_includeWhitespace_boxed_2770_, v_c_2768_, v_s_2769_);
lean_dec(v_tk_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2772_){
_start:
{
uint8_t v___y_2780_; uint32_t v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = 65;
v___x_2786_ = lean_uint32_dec_le(v___x_2785_, v_c_2772_);
if (v___x_2786_ == 0)
{
v___y_2780_ = v___x_2786_;
goto v___jp_2779_;
}
else
{
uint32_t v___x_2787_; uint8_t v___x_2788_; 
v___x_2787_ = 90;
v___x_2788_ = lean_uint32_dec_le(v_c_2772_, v___x_2787_);
v___y_2780_ = v___x_2788_;
goto v___jp_2779_;
}
v___jp_2773_:
{
uint32_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = 95;
v___x_2775_ = lean_uint32_dec_eq(v_c_2772_, v___x_2774_);
if (v___x_2775_ == 0)
{
uint8_t v___x_2776_; 
v___x_2776_ = l_Lean_isLetterLike(v_c_2772_);
if (v___x_2776_ == 0)
{
uint32_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = 171;
v___x_2778_ = lean_uint32_dec_eq(v_c_2772_, v___x_2777_);
return v___x_2778_;
}
else
{
return v___x_2776_;
}
}
else
{
return v___x_2775_;
}
}
v___jp_2779_:
{
if (v___y_2780_ == 0)
{
uint32_t v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = 97;
v___x_2782_ = lean_uint32_dec_le(v___x_2781_, v_c_2772_);
if (v___x_2782_ == 0)
{
goto v___jp_2773_;
}
else
{
uint32_t v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = 122;
v___x_2784_ = lean_uint32_dec_le(v_c_2772_, v___x_2783_);
if (v___x_2784_ == 0)
{
goto v___jp_2773_;
}
else
{
return v___x_2784_;
}
}
}
else
{
return v___y_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2789_){
_start:
{
uint32_t v_c_boxed_2790_; uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_c_boxed_2790_ = lean_unbox_uint32(v_c_2789_);
lean_dec(v_c_2789_);
v_res_2791_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2790_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2794_, lean_object* v_c_2795_, lean_object* v_s_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; lean_object* v_s_2801_; lean_object* v_stxStack_2802_; lean_object* v_errorMsg_2803_; uint8_t v___x_2804_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_box(0);
v___x_2799_ = 1;
v___x_2800_ = l_Lean_Parser_ParserState_next(v_s_2796_, v_c_2795_, v_startPos_2794_);
v_s_2801_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2794_, v___x_2797_, v___x_2799_, v___x_2798_, v_c_2795_, v___x_2800_);
v_stxStack_2802_ = lean_ctor_get(v_s_2801_, 0);
lean_inc_ref(v_stxStack_2802_);
v_errorMsg_2803_ = lean_ctor_get(v_s_2801_, 4);
lean_inc(v_errorMsg_2803_);
v___x_2804_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2803_, v___x_2797_);
lean_dec(v_errorMsg_2803_);
if (v___x_2804_ == 0)
{
lean_dec_ref(v_stxStack_2802_);
return v_s_2801_;
}
else
{
lean_object* v_stx_2805_; 
v_stx_2805_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2802_);
lean_dec_ref(v_stxStack_2802_);
if (lean_obj_tag(v_stx_2805_) == 3)
{
lean_object* v_rawVal_2806_; lean_object* v_info_2807_; lean_object* v_str_2808_; lean_object* v_startPos_2809_; lean_object* v_stopPos_2810_; lean_object* v_s_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_rawVal_2806_ = lean_ctor_get(v_stx_2805_, 1);
lean_inc_ref(v_rawVal_2806_);
v_info_2807_ = lean_ctor_get(v_stx_2805_, 0);
lean_inc(v_info_2807_);
lean_dec_ref_known(v_stx_2805_, 4);
v_str_2808_ = lean_ctor_get(v_rawVal_2806_, 0);
lean_inc_ref(v_str_2808_);
v_startPos_2809_ = lean_ctor_get(v_rawVal_2806_, 1);
lean_inc(v_startPos_2809_);
v_stopPos_2810_ = lean_ctor_get(v_rawVal_2806_, 2);
lean_inc(v_stopPos_2810_);
lean_dec_ref(v_rawVal_2806_);
v_s_2811_ = l_Lean_Parser_ParserState_popSyntax(v_s_2801_);
v___x_2812_ = lean_string_utf8_extract(v_str_2808_, v_startPos_2809_, v_stopPos_2810_);
lean_dec(v_stopPos_2810_);
lean_dec(v_startPos_2809_);
lean_dec_ref(v_str_2808_);
v___x_2813_ = l_Lean_Syntax_mkNameLit(v___x_2812_, v_info_2807_);
v___x_2814_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2811_, v___x_2813_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec(v_stx_2805_);
v___x_2815_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2816_ = l_Lean_Parser_ParserState_mkError(v_s_2801_, v___x_2815_);
return v___x_2816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2817_, lean_object* v_s_2818_){
_start:
{
lean_object* v_toInputContext_2819_; lean_object* v_pos_2820_; lean_object* v_tokens_2821_; lean_object* v_inputString_2822_; lean_object* v_endPos_2823_; uint32_t v_curr_2824_; uint32_t v___x_2825_; uint8_t v___x_2826_; uint8_t v___x_2827_; 
v_toInputContext_2819_ = lean_ctor_get(v_c_2817_, 0);
v_pos_2820_ = lean_ctor_get(v_s_2818_, 2);
v_tokens_2821_ = lean_ctor_get(v_c_2817_, 3);
v_inputString_2822_ = lean_ctor_get(v_toInputContext_2819_, 0);
v_endPos_2823_ = lean_ctor_get(v_toInputContext_2819_, 3);
v_curr_2824_ = lean_string_utf8_get(v_inputString_2822_, v_pos_2820_);
v___x_2825_ = 34;
v___x_2826_ = lean_uint32_dec_eq(v_curr_2824_, v___x_2825_);
v___x_2827_ = 1;
if (v___x_2826_ == 0)
{
uint32_t v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = 39;
v___x_2853_ = lean_uint32_dec_eq(v_curr_2824_, v___x_2852_);
if (v___x_2853_ == 0)
{
goto v___jp_2846_;
}
else
{
lean_object* v___x_2854_; uint32_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2854_ = lean_string_utf8_next(v_inputString_2822_, v_pos_2820_);
v___x_2855_ = lean_string_utf8_get(v_inputString_2822_, v___x_2854_);
lean_dec(v___x_2854_);
v___x_2856_ = lean_uint32_dec_eq(v___x_2855_, v___x_2852_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_inc(v_pos_2820_);
v___x_2857_ = l_Lean_Parser_ParserState_next(v_s_2818_, v_c_2817_, v_pos_2820_);
v___x_2858_ = l_Lean_Parser_charLitFnAux(v_pos_2820_, v_c_2817_, v___x_2857_);
return v___x_2858_;
}
else
{
goto v___jp_2846_;
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_inc(v_pos_2820_);
v___x_2859_ = l_Lean_Parser_ParserState_next(v_s_2818_, v_c_2817_, v_pos_2820_);
v___x_2860_ = l_Lean_Parser_strLitFnAux(v_pos_2820_, v___x_2827_, v_c_2817_, v___x_2859_);
return v___x_2860_;
}
v___jp_2828_:
{
lean_object* v_tk_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_inc(v_pos_2820_);
v_tk_2829_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2822_, v_tokens_2821_, v_pos_2820_, v_endPos_2823_);
v___x_2830_ = lean_box(0);
v___x_2831_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2820_, v_tk_2829_, v___x_2827_, v___x_2830_, v_c_2817_, v_s_2818_);
lean_dec(v_tk_2829_);
return v___x_2831_;
}
v___jp_2832_:
{
uint32_t v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = 114;
v___x_2834_ = lean_uint32_dec_eq(v_curr_2824_, v___x_2833_);
if (v___x_2834_ == 0)
{
goto v___jp_2828_;
}
else
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = lean_string_utf8_next(v_inputString_2822_, v_pos_2820_);
v___x_2836_ = l_Lean_Parser_isRawStrLitStart(v_c_2817_, v___x_2835_);
if (v___x_2836_ == 0)
{
goto v___jp_2828_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = l_Lean_Parser_ParserState_next(v_s_2818_, v_c_2817_, v_pos_2820_);
v___x_2838_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2820_, v_c_2817_, v___x_2837_);
return v___x_2838_;
}
}
}
v___jp_2839_:
{
uint32_t v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = 96;
v___x_2841_ = lean_uint32_dec_eq(v_curr_2824_, v___x_2840_);
if (v___x_2841_ == 0)
{
goto v___jp_2832_;
}
else
{
lean_object* v___x_2842_; uint32_t v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = lean_string_utf8_next(v_inputString_2822_, v_pos_2820_);
v___x_2843_ = lean_string_utf8_get(v_inputString_2822_, v___x_2842_);
lean_dec(v___x_2842_);
v___x_2844_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2843_);
if (v___x_2844_ == 0)
{
goto v___jp_2832_;
}
else
{
lean_object* v___x_2845_; 
v___x_2845_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2820_, v_c_2817_, v_s_2818_);
return v___x_2845_;
}
}
}
v___jp_2846_:
{
uint32_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = 48;
v___x_2848_ = lean_uint32_dec_le(v___x_2847_, v_curr_2824_);
if (v___x_2848_ == 0)
{
lean_inc(v_pos_2820_);
goto v___jp_2839_;
}
else
{
uint32_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = 57;
v___x_2850_ = lean_uint32_dec_le(v_curr_2824_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_inc(v_pos_2820_);
goto v___jp_2839_;
}
else
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Parser_numberFnAux(v___x_2827_, v_c_2817_, v_s_2818_);
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2861_, lean_object* v_s_2862_){
_start:
{
lean_object* v_cache_2863_; lean_object* v_errorMsg_2864_; 
v_cache_2863_ = lean_ctor_get(v_s_2862_, 3);
lean_inc_ref(v_cache_2863_);
v_errorMsg_2864_ = lean_ctor_get(v_s_2862_, 4);
if (lean_obj_tag(v_errorMsg_2864_) == 0)
{
lean_object* v_stxStack_2865_; lean_object* v_lhsPrec_2866_; lean_object* v_pos_2867_; lean_object* v_recoveredErrors_2868_; lean_object* v_parserCache_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2894_; 
v_stxStack_2865_ = lean_ctor_get(v_s_2862_, 0);
v_lhsPrec_2866_ = lean_ctor_get(v_s_2862_, 1);
v_pos_2867_ = lean_ctor_get(v_s_2862_, 2);
v_recoveredErrors_2868_ = lean_ctor_get(v_s_2862_, 5);
v_parserCache_2869_ = lean_ctor_get(v_cache_2863_, 1);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_cache_2863_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v_cache_2863_, 0);
lean_dec(v_unused_2895_);
v___x_2871_ = v_cache_2863_;
v_isShared_2872_ = v_isSharedCheck_2894_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_parserCache_2869_);
lean_dec(v_cache_2863_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2894_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2865_);
v___x_2874_ = lean_unsigned_to_nat(0u);
v___x_2875_ = lean_nat_dec_eq(v___x_2873_, v___x_2874_);
lean_dec(v___x_2873_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2887_; 
lean_inc_ref(v_recoveredErrors_2868_);
lean_inc(v_pos_2867_);
lean_inc(v_lhsPrec_2866_);
lean_inc(v_errorMsg_2864_);
lean_inc_ref(v_stxStack_2865_);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_s_2862_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; lean_object* v_unused_2889_; lean_object* v_unused_2890_; lean_object* v_unused_2891_; lean_object* v_unused_2892_; lean_object* v_unused_2893_; 
v_unused_2888_ = lean_ctor_get(v_s_2862_, 5);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_s_2862_, 4);
lean_dec(v_unused_2889_);
v_unused_2890_ = lean_ctor_get(v_s_2862_, 3);
lean_dec(v_unused_2890_);
v_unused_2891_ = lean_ctor_get(v_s_2862_, 2);
lean_dec(v_unused_2891_);
v_unused_2892_ = lean_ctor_get(v_s_2862_, 1);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_s_2862_, 0);
lean_dec(v_unused_2893_);
v___x_2877_ = v_s_2862_;
v_isShared_2878_ = v_isSharedCheck_2887_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v_s_2862_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2887_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_tk_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v_tk_2879_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2865_);
lean_inc(v_pos_2867_);
v___x_2880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2880_, 0, v_startPos_2861_);
lean_ctor_set(v___x_2880_, 1, v_pos_2867_);
lean_ctor_set(v___x_2880_, 2, v_tk_2879_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2880_);
v___x_2882_ = v___x_2871_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_parserCache_2869_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 3, v___x_2882_);
v___x_2884_ = v___x_2877_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_stxStack_2865_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_lhsPrec_2866_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_pos_2867_);
lean_ctor_set(v_reuseFailAlloc_2885_, 3, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2885_, 4, v_errorMsg_2864_);
lean_ctor_set(v_reuseFailAlloc_2885_, 5, v_recoveredErrors_2868_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_del_object(v___x_2871_);
lean_dec_ref(v_parserCache_2869_);
lean_dec(v_startPos_2861_);
return v_s_2862_;
}
}
}
else
{
lean_dec_ref(v_cache_2863_);
lean_dec(v_startPos_2861_);
return v_s_2862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2896_, lean_object* v_c_2897_, lean_object* v_s_2898_){
_start:
{
lean_object* v_pos_2899_; lean_object* v_cache_2900_; lean_object* v_toInputContext_2901_; uint8_t v___x_2902_; 
v_pos_2899_ = lean_ctor_get(v_s_2898_, 2);
v_cache_2900_ = lean_ctor_get(v_s_2898_, 3);
v_toInputContext_2901_ = lean_ctor_get(v_c_2897_, 0);
v___x_2902_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2901_, v_pos_2899_);
if (v___x_2902_ == 0)
{
lean_object* v_tokenCache_2903_; lean_object* v_startPos_2904_; lean_object* v_stopPos_2905_; lean_object* v_token_2906_; uint8_t v_decide_2907_; 
lean_dec(v_expected_2896_);
v_tokenCache_2903_ = lean_ctor_get(v_cache_2900_, 0);
v_startPos_2904_ = lean_ctor_get(v_tokenCache_2903_, 0);
v_stopPos_2905_ = lean_ctor_get(v_tokenCache_2903_, 1);
v_token_2906_ = lean_ctor_get(v_tokenCache_2903_, 2);
v_decide_2907_ = lean_nat_dec_eq(v_startPos_2904_, v_pos_2899_);
if (v_decide_2907_ == 0)
{
lean_object* v_s_2908_; lean_object* v___x_2909_; 
lean_inc(v_pos_2899_);
v_s_2908_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2897_, v_s_2898_);
v___x_2909_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2899_, v_s_2908_);
return v___x_2909_;
}
else
{
lean_object* v_s_2910_; lean_object* v___x_2911_; 
lean_inc(v_token_2906_);
lean_inc(v_stopPos_2905_);
lean_dec_ref(v_c_2897_);
v_s_2910_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2898_, v_token_2906_);
v___x_2911_ = l_Lean_Parser_ParserState_setPos(v_s_2910_, v_stopPos_2905_);
return v___x_2911_;
}
}
else
{
lean_object* v___x_2912_; 
lean_dec_ref(v_c_2897_);
v___x_2912_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2898_, v_expected_2896_);
return v___x_2912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2913_, lean_object* v_s_2914_){
_start:
{
lean_object* v_pos_2915_; lean_object* v_iniSz_2916_; lean_object* v___x_2917_; lean_object* v_s_2918_; lean_object* v_errorMsg_2919_; 
v_pos_2915_ = lean_ctor_get(v_s_2914_, 2);
lean_inc(v_pos_2915_);
v_iniSz_2916_ = l_Lean_Parser_ParserState_stackSize(v_s_2914_);
v___x_2917_ = lean_box(0);
v_s_2918_ = l_Lean_Parser_tokenFn(v___x_2917_, v_c_2913_, v_s_2914_);
v_errorMsg_2919_ = lean_ctor_get(v_s_2918_, 4);
lean_inc(v_errorMsg_2919_);
if (lean_obj_tag(v_errorMsg_2919_) == 1)
{
lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2928_; 
v_isSharedCheck_2928_ = !lean_is_exclusive(v_errorMsg_2919_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v_errorMsg_2919_, 0);
lean_dec(v_unused_2929_);
v___x_2921_ = v_errorMsg_2919_;
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
else
{
lean_dec(v_errorMsg_2919_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
lean_inc_ref(v_s_2918_);
v___x_2923_ = l_Lean_Parser_ParserState_restore(v_s_2918_, v_iniSz_2916_, v_pos_2915_);
lean_dec(v_iniSz_2916_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set_tag(v___x_2921_, 0);
lean_ctor_set(v___x_2921_, 0, v_s_2918_);
v___x_2925_ = v___x_2921_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_s_2918_);
v___x_2925_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2923_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
return v___x_2926_;
}
}
}
else
{
lean_object* v_stxStack_2930_; lean_object* v_stx_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_errorMsg_2919_);
v_stxStack_2930_ = lean_ctor_get(v_s_2918_, 0);
lean_inc_ref(v_stxStack_2930_);
v_stx_2931_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2930_);
lean_dec_ref(v_stxStack_2930_);
v___x_2932_ = l_Lean_Parser_ParserState_restore(v_s_2918_, v_iniSz_2916_, v_pos_2915_);
lean_dec(v_iniSz_2916_);
v___x_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2933_, 0, v_stx_2931_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2935_, lean_object* v_s_2936_){
_start:
{
lean_object* v_cache_2937_; lean_object* v_tokenCache_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2951_; 
v_cache_2937_ = lean_ctor_get(v_s_2936_, 3);
lean_inc_ref(v_cache_2937_);
v_tokenCache_2938_ = lean_ctor_get(v_cache_2937_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_cache_2937_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v_cache_2937_, 1);
lean_dec(v_unused_2952_);
v___x_2940_ = v_cache_2937_;
v_isShared_2941_ = v_isSharedCheck_2951_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_tokenCache_2938_);
lean_dec(v_cache_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2951_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_pos_2942_; lean_object* v_startPos_2943_; lean_object* v_token_2944_; uint8_t v_decide_2945_; 
v_pos_2942_ = lean_ctor_get(v_s_2936_, 2);
v_startPos_2943_ = lean_ctor_get(v_tokenCache_2938_, 0);
lean_inc(v_startPos_2943_);
v_token_2944_ = lean_ctor_get(v_tokenCache_2938_, 2);
lean_inc(v_token_2944_);
lean_dec_ref(v_tokenCache_2938_);
v_decide_2945_ = lean_nat_dec_eq(v_startPos_2943_, v_pos_2942_);
lean_dec(v_startPos_2943_);
if (v_decide_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec(v_token_2944_);
lean_del_object(v___x_2940_);
v___x_2946_ = l_Lean_Parser_peekTokenAux(v_c_2935_, v_s_2936_);
return v___x_2946_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_dec_ref(v_c_2935_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_token_2944_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_2947_);
lean_ctor_set(v___x_2940_, 0, v_s_2936_);
v___x_2949_ = v___x_2940_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_s_2936_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2953_, lean_object* v_c_2954_, lean_object* v_s_2955_){
_start:
{
lean_object* v_pos_2956_; lean_object* v_toInputContext_2957_; uint8_t v___x_2958_; 
v_pos_2956_ = lean_ctor_get(v_s_2955_, 2);
v_toInputContext_2957_ = lean_ctor_get(v_c_2954_, 0);
v___x_2958_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2957_, v_pos_2956_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_inc(v_pos_2956_);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_box(0);
v___x_2961_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2956_, v___x_2959_, v_includeWhitespace_2953_, v___x_2960_, v_c_2954_, v_s_2955_);
return v___x_2961_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec_ref(v_c_2954_);
v___x_2962_ = lean_box(0);
v___x_2963_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2955_, v___x_2962_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2964_, lean_object* v_c_2965_, lean_object* v_s_2966_){
_start:
{
uint8_t v_includeWhitespace_boxed_2967_; lean_object* v_res_2968_; 
v_includeWhitespace_boxed_2967_ = lean_unbox(v_includeWhitespace_2964_);
v_res_2968_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2967_, v_c_2965_, v_s_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_2969_, lean_object* v_expected_2970_, lean_object* v_c_2971_, lean_object* v_s_2972_){
_start:
{
lean_object* v_pos_2973_; lean_object* v_s_2974_; lean_object* v_stxStack_2975_; lean_object* v_errorMsg_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_pos_2973_ = lean_ctor_get(v_s_2972_, 2);
lean_inc(v_pos_2973_);
lean_inc(v_expected_2970_);
v_s_2974_ = l_Lean_Parser_tokenFn(v_expected_2970_, v_c_2971_, v_s_2972_);
v_stxStack_2975_ = lean_ctor_get(v_s_2974_, 0);
lean_inc_ref(v_stxStack_2975_);
v_errorMsg_2976_ = lean_ctor_get(v_s_2974_, 4);
lean_inc(v_errorMsg_2976_);
v___x_2977_ = lean_box(0);
v___x_2978_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2976_, v___x_2977_);
lean_dec(v_errorMsg_2976_);
if (v___x_2978_ == 0)
{
lean_dec_ref(v_stxStack_2975_);
lean_dec(v_pos_2973_);
lean_dec(v_expected_2970_);
lean_dec_ref(v_p_2969_);
return v_s_2974_;
}
else
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2975_);
lean_dec_ref(v_stxStack_2975_);
if (lean_obj_tag(v___x_2979_) == 2)
{
lean_object* v_val_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v_val_2980_ = lean_ctor_get(v___x_2979_, 1);
lean_inc_ref(v_val_2980_);
lean_dec_ref_known(v___x_2979_, 2);
v___x_2981_ = lean_apply_1(v_p_2969_, v_val_2980_);
v___x_2982_ = lean_unbox(v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2974_, v_expected_2970_, v_pos_2973_);
return v___x_2983_;
}
else
{
lean_dec(v_pos_2973_);
lean_dec(v_expected_2970_);
return v_s_2974_;
}
}
else
{
lean_object* v___x_2984_; 
lean_dec(v___x_2979_);
lean_dec_ref(v_p_2969_);
v___x_2984_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2974_, v_expected_2970_, v_pos_2973_);
return v___x_2984_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_2985_, lean_object* v_s_2986_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_string_dec_eq(v_s_2986_, v_sym_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_2988_, lean_object* v_s_2989_){
_start:
{
uint8_t v_res_2990_; lean_object* v_r_2991_; 
v_res_2990_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_2988_, v_s_2989_);
lean_dec_ref(v_s_2989_);
lean_dec_ref(v_sym_2988_);
v_r_2991_ = lean_box(v_res_2990_);
return v_r_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_2992_, lean_object* v_errorMsg_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2996_, 0, v_sym_2992_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_errorMsg_2993_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Lean_Parser_satisfySymbolFn(v___f_2996_, v___x_2998_, v_a_2994_, v_a_2995_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_3000_, lean_object* v_tks_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_sym_3000_);
lean_ctor_set(v___x_3002_, 1, v_tks_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_inc_ref(v_sym_3003_);
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3004_, 0, v_sym_3003_);
v___f_3005_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_sym_3003_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3009_, 0, v___f_3004_);
lean_ctor_set(v___x_3009_, 1, v___f_3005_);
lean_ctor_set(v___x_3009_, 2, v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3013_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3014_ = lean_string_append(v___x_3013_, v_sym_3010_);
v___x_3015_ = lean_string_append(v___x_3014_, v___x_3013_);
v___x_3016_ = l_Lean_Parser_symbolFnAux(v_sym_3010_, v___x_3015_, v_a_3011_, v_a_3012_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3017_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v_str_3022_; lean_object* v_startInclusive_3023_; lean_object* v_endExclusive_3024_; lean_object* v_sym_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_string_utf8_byte_size(v_sym_3017_);
v___x_3020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3020_, 0, v_sym_3017_);
lean_ctor_set(v___x_3020_, 1, v___x_3018_);
lean_ctor_set(v___x_3020_, 2, v___x_3019_);
v___x_3021_ = l_String_Slice_trimAscii(v___x_3020_);
v_str_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_ref(v_str_3022_);
v_startInclusive_3023_ = lean_ctor_get(v___x_3021_, 1);
lean_inc(v_startInclusive_3023_);
v_endExclusive_3024_ = lean_ctor_get(v___x_3021_, 2);
lean_inc(v_endExclusive_3024_);
lean_dec_ref(v___x_3021_);
v_sym_3025_ = lean_string_utf8_extract_fast(v_str_3022_, v_startInclusive_3023_, v_endExclusive_3024_);
lean_dec(v_endExclusive_3024_);
lean_dec(v_startInclusive_3023_);
lean_dec_ref(v_str_3022_);
lean_inc_ref(v_sym_3025_);
v___x_3026_ = l_Lean_Parser_symbolInfo(v_sym_3025_);
v___x_3027_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3027_, 0, v_sym_3025_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3029_, lean_object* v_errorMsg_3030_, lean_object* v_c_3031_, lean_object* v_s_3032_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v_s_3035_; lean_object* v_stxStack_3039_; lean_object* v_errorMsg_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3033_ = lean_box(0);
lean_inc_ref(v_errorMsg_3030_);
v___x_3034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_errorMsg_3030_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v_s_3035_ = l_Lean_Parser_tokenFn(v___x_3034_, v_c_3031_, v_s_3032_);
v_stxStack_3039_ = lean_ctor_get(v_s_3035_, 0);
lean_inc_ref(v_stxStack_3039_);
v_errorMsg_3040_ = lean_ctor_get(v_s_3035_, 4);
lean_inc(v_errorMsg_3040_);
v___x_3041_ = lean_box(0);
v___x_3042_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3040_, v___x_3041_);
lean_dec(v_errorMsg_3040_);
if (v___x_3042_ == 0)
{
lean_dec_ref(v_stxStack_3039_);
lean_dec_ref(v_errorMsg_3030_);
lean_dec_ref(v_sym_3029_);
return v_s_3035_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3039_);
lean_dec_ref(v_stxStack_3039_);
switch(lean_obj_tag(v___x_3043_))
{
case 2:
{
lean_object* v_val_3044_; uint8_t v___x_3045_; 
v_val_3044_ = lean_ctor_get(v___x_3043_, 1);
lean_inc_ref(v_val_3044_);
lean_dec_ref_known(v___x_3043_, 2);
v___x_3045_ = lean_string_dec_eq(v_sym_3029_, v_val_3044_);
lean_dec_ref(v_val_3044_);
lean_dec_ref(v_sym_3029_);
if (v___x_3045_ == 0)
{
goto v___jp_3036_;
}
else
{
lean_dec_ref(v_errorMsg_3030_);
return v_s_3035_;
}
}
case 3:
{
lean_object* v_rawVal_3046_; lean_object* v_info_3047_; lean_object* v_str_3048_; lean_object* v_startPos_3049_; lean_object* v_stopPos_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v_rawVal_3046_ = lean_ctor_get(v___x_3043_, 1);
lean_inc_ref(v_rawVal_3046_);
v_info_3047_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_info_3047_);
lean_dec_ref_known(v___x_3043_, 4);
v_str_3048_ = lean_ctor_get(v_rawVal_3046_, 0);
lean_inc_ref(v_str_3048_);
v_startPos_3049_ = lean_ctor_get(v_rawVal_3046_, 1);
lean_inc(v_startPos_3049_);
v_stopPos_3050_ = lean_ctor_get(v_rawVal_3046_, 2);
lean_inc(v_stopPos_3050_);
lean_dec_ref(v_rawVal_3046_);
v___x_3051_ = lean_string_utf8_extract(v_str_3048_, v_startPos_3049_, v_stopPos_3050_);
lean_dec(v_stopPos_3050_);
lean_dec(v_startPos_3049_);
lean_dec_ref(v_str_3048_);
v___x_3052_ = lean_string_dec_eq(v_sym_3029_, v___x_3051_);
lean_dec_ref(v___x_3051_);
if (v___x_3052_ == 0)
{
lean_dec(v_info_3047_);
lean_dec_ref(v_sym_3029_);
goto v___jp_3036_;
}
else
{
lean_object* v_s_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref(v_errorMsg_3030_);
v_s_3053_ = l_Lean_Parser_ParserState_popSyntax(v_s_3035_);
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v_info_3047_);
lean_ctor_set(v___x_3054_, 1, v_sym_3029_);
v___x_3055_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3053_, v___x_3054_);
return v___x_3055_;
}
}
default: 
{
lean_dec(v___x_3043_);
lean_dec_ref(v_sym_3029_);
goto v___jp_3036_;
}
}
}
v___jp_3036_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3035_, v_errorMsg_3030_, v___x_3037_);
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3059_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3060_ = lean_string_append(v___x_3059_, v_sym_3056_);
v___x_3061_ = lean_string_append(v___x_3060_, v___x_3059_);
v___x_3062_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3056_, v___x_3061_, v_a_3057_, v_a_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3067_, uint8_t v_includeIdent_3068_){
_start:
{
lean_object* v___f_3069_; lean_object* v___f_3070_; 
v___f_3069_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3070_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3068_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_sym_3067_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3074_, 0, v___f_3069_);
lean_ctor_set(v___x_3074_, 1, v___f_3070_);
lean_ctor_set(v___x_3074_, 2, v___x_3073_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3075_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_sym_3067_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___f_3069_);
lean_ctor_set(v___x_3078_, 1, v___f_3070_);
lean_ctor_set(v___x_3078_, 2, v___x_3077_);
return v___x_3078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3079_, lean_object* v_includeIdent_3080_){
_start:
{
uint8_t v_includeIdent_boxed_3081_; lean_object* v_res_3082_; 
v_includeIdent_boxed_3081_ = lean_unbox(v_includeIdent_3080_);
v_res_3082_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3079_, v_includeIdent_boxed_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3083_, uint8_t v_includeIdent_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_str_3089_; lean_object* v_startInclusive_3090_; lean_object* v_endExclusive_3091_; lean_object* v_sym_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_string_utf8_byte_size(v_sym_3083_);
v___x_3087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3087_, 0, v_sym_3083_);
lean_ctor_set(v___x_3087_, 1, v___x_3085_);
lean_ctor_set(v___x_3087_, 2, v___x_3086_);
v___x_3088_ = l_String_Slice_trimAscii(v___x_3087_);
v_str_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc_ref(v_str_3089_);
v_startInclusive_3090_ = lean_ctor_get(v___x_3088_, 1);
lean_inc(v_startInclusive_3090_);
v_endExclusive_3091_ = lean_ctor_get(v___x_3088_, 2);
lean_inc(v_endExclusive_3091_);
lean_dec_ref(v___x_3088_);
v_sym_3092_ = lean_string_utf8_extract_fast(v_str_3089_, v_startInclusive_3090_, v_endExclusive_3091_);
lean_dec(v_endExclusive_3091_);
lean_dec(v_startInclusive_3090_);
lean_dec_ref(v_str_3089_);
lean_inc_ref(v_sym_3092_);
v___x_3093_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3092_, v_includeIdent_3084_);
v___x_3094_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3094_, 0, v_sym_3092_);
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3096_, lean_object* v_includeIdent_3097_){
_start:
{
uint8_t v_includeIdent_boxed_3098_; lean_object* v_res_3099_; 
v_includeIdent_boxed_3098_ = lean_unbox(v_includeIdent_3097_);
v_res_3099_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3096_, v_includeIdent_boxed_3098_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3100_, lean_object* v_errorMsg_3101_, lean_object* v_j_3102_, lean_object* v_c_3103_, lean_object* v_s_3104_){
_start:
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_string_utf8_at_end(v_sym_3100_, v_j_3102_);
if (v___x_3105_ == 0)
{
lean_object* v_pos_3106_; lean_object* v_toInputContext_3107_; uint8_t v___x_3108_; 
v_pos_3106_ = lean_ctor_get(v_s_3104_, 2);
v_toInputContext_3107_ = lean_ctor_get(v_c_3103_, 0);
v___x_3108_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3107_, v_pos_3106_);
if (v___x_3108_ == 0)
{
lean_object* v_inputString_3109_; uint32_t v___x_3110_; uint32_t v___x_3111_; uint8_t v___x_3112_; 
v_inputString_3109_ = lean_ctor_get(v_toInputContext_3107_, 0);
v___x_3110_ = lean_string_utf8_get_fast(v_sym_3100_, v_j_3102_);
v___x_3111_ = lean_string_utf8_get_fast(v_inputString_3109_, v_pos_3106_);
v___x_3112_ = lean_uint32_dec_eq(v___x_3110_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec(v_j_3102_);
v___x_3113_ = l_Lean_Parser_ParserState_mkError(v_s_3104_, v_errorMsg_3101_);
return v___x_3113_;
}
else
{
if (v___x_3108_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_inc(v_pos_3106_);
v___x_3114_ = lean_string_utf8_next_fast(v_sym_3100_, v_j_3102_);
lean_dec(v_j_3102_);
v___x_3115_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3104_, v_c_3103_, v_pos_3106_);
lean_dec(v_pos_3106_);
v_j_3102_ = v___x_3114_;
v_s_3104_ = v___x_3115_;
goto _start;
}
else
{
lean_object* v___x_3117_; 
lean_dec(v_j_3102_);
v___x_3117_ = l_Lean_Parser_ParserState_mkError(v_s_3104_, v_errorMsg_3101_);
return v___x_3117_;
}
}
}
else
{
lean_object* v___x_3118_; 
lean_dec(v_j_3102_);
v___x_3118_ = l_Lean_Parser_ParserState_mkError(v_s_3104_, v_errorMsg_3101_);
return v___x_3118_;
}
}
else
{
lean_dec(v_j_3102_);
lean_dec_ref(v_errorMsg_3101_);
return v_s_3104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3119_, lean_object* v_errorMsg_3120_, lean_object* v_j_3121_, lean_object* v_c_3122_, lean_object* v_s_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3119_, v_errorMsg_3120_, v_j_3121_, v_c_3122_, v_s_3123_);
lean_dec_ref(v_c_3122_);
lean_dec_ref(v_sym_3119_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3125_, lean_object* v_errorMsg_3126_, lean_object* v_j_3127_, lean_object* v_c_3128_, lean_object* v_s_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3125_, v_errorMsg_3126_, v_j_3127_, v_c_3128_, v_s_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3131_, lean_object* v_errorMsg_3132_, lean_object* v_j_3133_, lean_object* v_c_3134_, lean_object* v_s_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Parser_strAux(v_sym_3131_, v_errorMsg_3132_, v_j_3133_, v_c_3134_, v_s_3135_);
lean_dec_ref(v_c_3134_);
lean_dec_ref(v_sym_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3137_, lean_object* v_i_3138_){
_start:
{
lean_object* v_zero_3139_; uint8_t v_isZero_3140_; 
v_zero_3139_ = lean_unsigned_to_nat(0u);
v_isZero_3140_ = lean_nat_dec_eq(v_i_3138_, v_zero_3139_);
if (v_isZero_3140_ == 1)
{
lean_object* v___x_3141_; 
lean_dec(v_i_3138_);
v___x_3141_ = lean_box(0);
return v___x_3141_;
}
else
{
lean_object* v_one_3142_; lean_object* v_n_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_one_3142_ = lean_unsigned_to_nat(1u);
v_n_3143_ = lean_nat_sub(v_i_3138_, v_one_3142_);
lean_dec(v_i_3138_);
v___x_3144_ = l_Subarray_get___redArg(v_as_3137_, v_n_3143_);
v___x_3145_ = l_Lean_Syntax_isNone(v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; 
lean_dec(v_n_3143_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
return v___x_3146_;
}
else
{
lean_dec(v___x_3144_);
v_i_3138_ = v_n_3143_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3148_, lean_object* v_i_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3148_, v_i_3149_);
lean_dec_ref(v_as_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3151_){
_start:
{
lean_object* v___x_3152_; lean_object* v_start_3153_; lean_object* v_stop_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3152_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3151_);
v_start_3153_ = lean_ctor_get(v___x_3152_, 1);
lean_inc(v_start_3153_);
v_stop_3154_ = lean_ctor_get(v___x_3152_, 2);
lean_inc(v_stop_3154_);
v___x_3155_ = lean_nat_sub(v_stop_3154_, v_start_3153_);
lean_dec(v_start_3153_);
lean_dec(v_stop_3154_);
v___x_3156_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3152_, v___x_3155_);
lean_dec_ref(v___x_3152_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_box(0);
return v___x_3157_;
}
else
{
lean_object* v_val_3158_; 
v_val_3158_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_val_3158_);
lean_dec_ref_known(v___x_3156_, 1);
return v_val_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3159_, lean_object* v_i_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3159_, v_i_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3163_, lean_object* v_i_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3163_, v_i_3164_, v_a_3165_);
lean_dec_ref(v_as_3163_);
return v_res_3166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_Syntax_getTailInfo(v_prev_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_trailing_3169_; lean_object* v_startPos_3170_; lean_object* v_stopPos_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_trailing_3169_ = lean_ctor_get(v___x_3168_, 2);
lean_inc_ref(v_trailing_3169_);
lean_dec_ref_known(v___x_3168_, 4);
v_startPos_3170_ = lean_ctor_get(v_trailing_3169_, 1);
lean_inc(v_startPos_3170_);
v_stopPos_3171_ = lean_ctor_get(v_trailing_3169_, 2);
lean_inc(v_stopPos_3171_);
lean_dec_ref(v_trailing_3169_);
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_nat_add(v_startPos_3170_, v___x_3172_);
lean_dec(v_startPos_3170_);
v___x_3174_ = lean_nat_dec_le(v___x_3173_, v_stopPos_3171_);
lean_dec(v_stopPos_3171_);
lean_dec(v___x_3173_);
return v___x_3174_;
}
else
{
uint8_t v___x_3175_; 
lean_dec(v___x_3168_);
v___x_3175_ = 0;
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3176_){
_start:
{
uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_res_3177_ = l_Lean_Parser_checkTailWs(v_prev_3176_);
lean_dec(v_prev_3176_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3179_, lean_object* v_s_3180_){
_start:
{
lean_object* v_stxStack_3181_; lean_object* v_prev_3182_; uint8_t v___x_3183_; 
v_stxStack_3181_ = lean_ctor_get(v_s_3180_, 0);
lean_inc_ref(v_stxStack_3181_);
v_prev_3182_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3181_);
v___x_3183_ = l_Lean_Parser_checkTailWs(v_prev_3182_);
lean_dec(v_prev_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Parser_ParserState_mkError(v_s_3180_, v_errorMsg_3179_);
return v___x_3184_;
}
else
{
lean_dec_ref(v_errorMsg_3179_);
return v_s_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3185_, lean_object* v_x_3186_, lean_object* v_s_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3185_, v_s_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3189_, lean_object* v_x_3190_, lean_object* v_s_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3189_, v_x_3190_, v_s_3191_);
lean_dec_ref(v_x_3190_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3193_){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3195_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3195_, 0, v_errorMsg_3193_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3205_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3206_ = l_Lean_addBuiltinDocString(v___x_3204_, v___x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3209_){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = l_String_instInhabitedSlice;
v___x_3211_ = lean_panic_fn_borrowed(v___x_3210_, v_msg_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3212_, lean_object* v_a_3213_, uint8_t v_b_3214_){
_start:
{
lean_object* v_str_3215_; lean_object* v_startInclusive_3216_; lean_object* v_endExclusive_3217_; lean_object* v___x_3218_; uint8_t v_decide_3219_; 
v_str_3215_ = lean_ctor_get(v_s_3212_, 0);
v_startInclusive_3216_ = lean_ctor_get(v_s_3212_, 1);
v_endExclusive_3217_ = lean_ctor_get(v_s_3212_, 2);
v___x_3218_ = lean_nat_sub(v_endExclusive_3217_, v_startInclusive_3216_);
v_decide_3219_ = lean_nat_dec_eq(v_a_3213_, v___x_3218_);
lean_dec(v___x_3218_);
if (v_decide_3219_ == 0)
{
uint32_t v___x_3220_; lean_object* v___x_3221_; uint32_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3220_ = 10;
v___x_3221_ = lean_nat_add(v_startInclusive_3216_, v_a_3213_);
lean_dec(v_a_3213_);
v___x_3222_ = lean_string_utf8_get_fast(v_str_3215_, v___x_3221_);
v___x_3223_ = lean_uint32_dec_eq(v___x_3222_, v___x_3220_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_string_utf8_next_fast(v_str_3215_, v___x_3221_);
lean_dec(v___x_3221_);
v___x_3225_ = lean_nat_sub(v___x_3224_, v_startInclusive_3216_);
v_a_3213_ = v___x_3225_;
v_b_3214_ = v___x_3223_;
goto _start;
}
else
{
lean_dec(v___x_3221_);
return v___x_3223_;
}
}
else
{
lean_dec(v_a_3213_);
return v_b_3214_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3227_, lean_object* v_a_3228_, lean_object* v_b_3229_){
_start:
{
uint8_t v_b_boxed_3230_; uint8_t v_res_3231_; lean_object* v_r_3232_; 
v_b_boxed_3230_ = lean_unbox(v_b_3229_);
v_res_3231_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3227_, v_a_3228_, v_b_boxed_3230_);
lean_dec_ref(v_s_3227_);
v_r_3232_ = lean_box(v_res_3231_);
return v_r_3232_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3233_){
_start:
{
lean_object* v_searcher_3234_; uint8_t v___x_3235_; uint8_t v___x_3236_; 
v_searcher_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = 0;
v___x_3236_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3233_, v_searcher_3234_, v___x_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3237_);
lean_dec_ref(v_s_3237_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3243_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3244_ = lean_unsigned_to_nat(14u);
v___x_3245_ = lean_unsigned_to_nat(22u);
v___x_3246_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3247_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3248_ = l_mkPanicMessageWithDecl(v___x_3247_, v___x_3246_, v___x_3245_, v___x_3244_, v___x_3243_);
return v___x_3248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_Syntax_getTailInfo(v_prev_3249_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_trailing_3251_; lean_object* v_str_3252_; lean_object* v_startPos_3253_; lean_object* v_stopPos_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3272_; 
v_trailing_3251_ = lean_ctor_get(v___x_3250_, 2);
lean_inc_ref(v_trailing_3251_);
lean_dec_ref_known(v___x_3250_, 4);
v_str_3252_ = lean_ctor_get(v_trailing_3251_, 0);
v_startPos_3253_ = lean_ctor_get(v_trailing_3251_, 1);
v_stopPos_3254_ = lean_ctor_get(v_trailing_3251_, 2);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_trailing_3251_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3256_ = v_trailing_3251_;
v_isShared_3257_ = v_isSharedCheck_3272_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_stopPos_3254_);
lean_inc(v_startPos_3253_);
lean_inc(v_str_3252_);
lean_dec(v_trailing_3251_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3272_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
uint8_t v___y_3259_; uint8_t v___x_3267_; uint8_t v___y_3269_; uint8_t v___x_3270_; 
v___x_3267_ = lean_string_is_valid_pos(v_str_3252_, v_startPos_3253_);
v___x_3270_ = lean_string_is_valid_pos(v_str_3252_, v_stopPos_3254_);
if (v___x_3270_ == 0)
{
v___y_3269_ = v___x_3270_;
goto v___jp_3268_;
}
else
{
uint8_t v___x_3271_; 
v___x_3271_ = lean_nat_dec_le(v_startPos_3253_, v_stopPos_3254_);
v___y_3269_ = v___x_3271_;
goto v___jp_3268_;
}
v___jp_3258_:
{
if (v___y_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
lean_del_object(v___x_3256_);
lean_dec(v_stopPos_3254_);
lean_dec(v_startPos_3253_);
lean_dec_ref(v_str_3252_);
v___x_3260_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3261_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3260_);
v___x_3262_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3261_);
lean_dec_ref(v___x_3261_);
return v___x_3262_;
}
else
{
lean_object* v___x_3264_; 
if (v_isShared_3257_ == 0)
{
v___x_3264_ = v___x_3256_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_str_3252_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_startPos_3253_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_stopPos_3254_);
v___x_3264_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
uint8_t v___x_3265_; 
v___x_3265_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3264_);
lean_dec_ref(v___x_3264_);
return v___x_3265_;
}
}
}
v___jp_3268_:
{
if (v___x_3267_ == 0)
{
v___y_3259_ = v___x_3267_;
goto v___jp_3258_;
}
else
{
v___y_3259_ = v___y_3269_;
goto v___jp_3258_;
}
}
}
}
else
{
uint8_t v___x_3273_; 
lean_dec(v___x_3250_);
v___x_3273_ = 0;
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l_Lean_Parser_checkTailLinebreak(v_prev_3274_);
lean_dec(v_prev_3274_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3277_, lean_object* v_inst_3278_, lean_object* v_R_3279_, lean_object* v_a_3280_, uint8_t v_b_3281_, lean_object* v_c_3282_){
_start:
{
uint8_t v___x_3283_; 
v___x_3283_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3277_, v_a_3280_, v_b_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3284_, lean_object* v_inst_3285_, lean_object* v_R_3286_, lean_object* v_a_3287_, lean_object* v_b_3288_, lean_object* v_c_3289_){
_start:
{
uint8_t v_b_boxed_3290_; uint8_t v_res_3291_; lean_object* v_r_3292_; 
v_b_boxed_3290_ = lean_unbox(v_b_3288_);
v_res_3291_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3284_, v_inst_3285_, v_R_3286_, v_a_3287_, v_b_boxed_3290_, v_c_3289_);
lean_dec_ref(v_s_3284_);
v_r_3292_ = lean_box(v_res_3291_);
return v_r_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3293_, lean_object* v_s_3294_){
_start:
{
lean_object* v_stxStack_3295_; lean_object* v_prev_3296_; uint8_t v___x_3297_; 
v_stxStack_3295_ = lean_ctor_get(v_s_3294_, 0);
v_prev_3296_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3295_);
v___x_3297_ = l_Lean_Parser_checkTailLinebreak(v_prev_3296_);
lean_dec(v_prev_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Parser_ParserState_mkError(v_s_3294_, v_errorMsg_3293_);
return v___x_3298_;
}
else
{
lean_dec_ref(v_errorMsg_3293_);
return v_s_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3299_, lean_object* v_x_3300_, lean_object* v_s_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3299_, v_s_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3303_, lean_object* v_x_3304_, lean_object* v_s_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3303_, v_x_3304_, v_s_3305_);
lean_dec_ref(v_x_3304_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3309_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3309_, 0, v_errorMsg_3307_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3319_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3320_ = l_Lean_addBuiltinDocString(v___x_3318_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3322_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Syntax_getTailInfo(v_prev_3323_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_trailing_3325_; lean_object* v_startPos_3326_; lean_object* v_stopPos_3327_; uint8_t v_decide_3328_; 
v_trailing_3325_ = lean_ctor_get(v___x_3324_, 2);
lean_inc_ref(v_trailing_3325_);
lean_dec_ref_known(v___x_3324_, 4);
v_startPos_3326_ = lean_ctor_get(v_trailing_3325_, 1);
lean_inc(v_startPos_3326_);
v_stopPos_3327_ = lean_ctor_get(v_trailing_3325_, 2);
lean_inc(v_stopPos_3327_);
lean_dec_ref(v_trailing_3325_);
v_decide_3328_ = lean_nat_dec_eq(v_stopPos_3327_, v_startPos_3326_);
lean_dec(v_startPos_3326_);
lean_dec(v_stopPos_3327_);
return v_decide_3328_;
}
else
{
uint8_t v___x_3329_; 
lean_dec(v___x_3324_);
v___x_3329_ = 0;
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3330_){
_start:
{
uint8_t v_res_3331_; lean_object* v_r_3332_; 
v_res_3331_ = l_Lean_Parser_checkTailNoWs(v_prev_3330_);
lean_dec(v_prev_3330_);
v_r_3332_ = lean_box(v_res_3331_);
return v_r_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3333_, lean_object* v_s_3334_){
_start:
{
lean_object* v_stxStack_3335_; lean_object* v_prev_3336_; uint8_t v___x_3337_; 
v_stxStack_3335_ = lean_ctor_get(v_s_3334_, 0);
lean_inc_ref(v_stxStack_3335_);
v_prev_3336_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3335_);
v___x_3337_ = l_Lean_Parser_checkTailNoWs(v_prev_3336_);
lean_dec(v_prev_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Parser_ParserState_mkError(v_s_3334_, v_errorMsg_3333_);
return v___x_3338_;
}
else
{
lean_dec_ref(v_errorMsg_3333_);
return v_s_3334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3339_, lean_object* v_x_3340_, lean_object* v_s_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3339_, v_s_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3343_, lean_object* v_x_3344_, lean_object* v_s_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3343_, v_x_3344_, v_s_3345_);
lean_dec_ref(v_x_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3347_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3349_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3349_, 0, v_errorMsg_3347_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3358_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3359_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3360_ = l_Lean_addBuiltinDocString(v___x_3358_, v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3362_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3363_, lean_object* v_asciiSym_3364_, lean_object* v_s_3365_){
_start:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_string_dec_eq(v_s_3365_, v_sym_3363_);
if (v___x_3366_ == 0)
{
uint8_t v___x_3367_; 
v___x_3367_ = lean_string_dec_eq(v_s_3365_, v_asciiSym_3364_);
return v___x_3367_;
}
else
{
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3368_, lean_object* v_asciiSym_3369_, lean_object* v_s_3370_){
_start:
{
uint8_t v_res_3371_; lean_object* v_r_3372_; 
v_res_3371_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3368_, v_asciiSym_3369_, v_s_3370_);
lean_dec_ref(v_s_3370_);
lean_dec_ref(v_asciiSym_3369_);
lean_dec_ref(v_sym_3368_);
v_r_3372_ = lean_box(v_res_3371_);
return v_r_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3373_, lean_object* v_asciiSym_3374_, lean_object* v_expected_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v___f_3378_; lean_object* v___x_3379_; 
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3378_, 0, v_sym_3373_);
lean_closure_set(v___f_3378_, 1, v_asciiSym_3374_);
v___x_3379_ = l_Lean_Parser_satisfySymbolFn(v___f_3378_, v_expected_3375_, v_a_3376_, v_a_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3380_, lean_object* v_sym_3381_, lean_object* v_tks_3382_){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v_asciiSym_3380_);
lean_ctor_set(v___x_3383_, 1, v_tks_3382_);
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v_sym_3381_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3385_, lean_object* v_asciiSym_3386_){
_start:
{
lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_inc_ref(v_sym_3385_);
lean_inc_ref(v_asciiSym_3386_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3387_, 0, v_asciiSym_3386_);
lean_closure_set(v___f_3387_, 1, v_sym_3385_);
v___f_3388_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v_asciiSym_3386_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_sym_3385_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3393_, 0, v___f_3387_);
lean_ctor_set(v___x_3393_, 1, v___f_3388_);
lean_ctor_set(v___x_3393_, 2, v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3395_, lean_object* v_asciiSym_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3399_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3400_ = lean_string_append(v___x_3399_, v_sym_3395_);
v___x_3401_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3402_ = lean_string_append(v___x_3400_, v___x_3401_);
v___x_3403_ = lean_string_append(v___x_3402_, v_asciiSym_3396_);
v___x_3404_ = lean_string_append(v___x_3403_, v___x_3399_);
v___x_3405_ = lean_box(0);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3395_, v_asciiSym_3396_, v___x_3406_, v_a_3397_, v_a_3398_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3408_, lean_object* v_asciiSym_3409_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v_str_3414_; lean_object* v_startInclusive_3415_; lean_object* v_endExclusive_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3433_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = lean_string_utf8_byte_size(v_sym_3408_);
v___x_3412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3412_, 0, v_sym_3408_);
lean_ctor_set(v___x_3412_, 1, v___x_3410_);
lean_ctor_set(v___x_3412_, 2, v___x_3411_);
v___x_3413_ = l_String_Slice_trimAscii(v___x_3412_);
v_str_3414_ = lean_ctor_get(v___x_3413_, 0);
v_startInclusive_3415_ = lean_ctor_get(v___x_3413_, 1);
v_endExclusive_3416_ = lean_ctor_get(v___x_3413_, 2);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3418_ = v___x_3413_;
v_isShared_3419_ = v_isSharedCheck_3433_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_endExclusive_3416_);
lean_inc(v_startInclusive_3415_);
lean_inc(v_str_3414_);
lean_dec(v___x_3413_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3433_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_string_utf8_byte_size(v_asciiSym_3409_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 2, v___x_3420_);
lean_ctor_set(v___x_3418_, 1, v___x_3410_);
lean_ctor_set(v___x_3418_, 0, v_asciiSym_3409_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_asciiSym_3409_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v_str_3424_; lean_object* v_startInclusive_3425_; lean_object* v_endExclusive_3426_; lean_object* v_sym_3427_; lean_object* v_asciiSym_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3423_ = l_String_Slice_trimAscii(v___x_3422_);
v_str_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_str_3424_);
v_startInclusive_3425_ = lean_ctor_get(v___x_3423_, 1);
lean_inc(v_startInclusive_3425_);
v_endExclusive_3426_ = lean_ctor_get(v___x_3423_, 2);
lean_inc(v_endExclusive_3426_);
lean_dec_ref(v___x_3423_);
v_sym_3427_ = lean_string_utf8_extract_fast(v_str_3414_, v_startInclusive_3415_, v_endExclusive_3416_);
lean_dec(v_endExclusive_3416_);
lean_dec(v_startInclusive_3415_);
lean_dec_ref(v_str_3414_);
v_asciiSym_3428_ = lean_string_utf8_extract_fast(v_str_3424_, v_startInclusive_3425_, v_endExclusive_3426_);
lean_dec(v_endExclusive_3426_);
lean_dec(v_startInclusive_3425_);
lean_dec_ref(v_str_3424_);
lean_inc_ref(v_asciiSym_3428_);
lean_inc_ref(v_sym_3427_);
v___x_3429_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3427_, v_asciiSym_3428_);
v___x_3430_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3430_, 0, v_sym_3427_);
lean_closure_set(v___x_3430_, 1, v_asciiSym_3428_);
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
return v___x_3431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3434_, lean_object* v_asciiSym_3435_, uint8_t v_preserveForPP_3436_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3434_, v_asciiSym_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3438_, lean_object* v_asciiSym_3439_, lean_object* v_preserveForPP_3440_){
_start:
{
uint8_t v_preserveForPP_boxed_3441_; lean_object* v_res_3442_; 
v_preserveForPP_boxed_3441_ = lean_unbox(v_preserveForPP_3440_);
v_res_3442_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3438_, v_asciiSym_3439_, v_preserveForPP_boxed_3441_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3443_){
_start:
{
lean_object* v___f_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___f_3444_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3445_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3446_ = lean_box(0);
v___x_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_k_3443_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
v___x_3449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3449_, 0, v___f_3444_);
lean_ctor_set(v___x_3449_, 1, v___f_3445_);
lean_ctor_set(v___x_3449_, 2, v___x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3450_, lean_object* v_desc_3451_, lean_object* v_c_3452_, lean_object* v_s_3453_){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v_s_3456_; lean_object* v_stxStack_3457_; lean_object* v_errorMsg_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; 
v___x_3454_ = lean_box(0);
lean_inc_ref(v_desc_3451_);
v___x_3455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3455_, 0, v_desc_3451_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v_s_3456_ = l_Lean_Parser_tokenFn(v___x_3455_, v_c_3452_, v_s_3453_);
v_stxStack_3457_ = lean_ctor_get(v_s_3456_, 0);
lean_inc_ref(v_stxStack_3457_);
v_errorMsg_3458_ = lean_ctor_get(v_s_3456_, 4);
lean_inc(v_errorMsg_3458_);
v___x_3459_ = lean_box(0);
v___x_3460_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3458_, v___x_3459_);
lean_dec(v_errorMsg_3458_);
if (v___x_3460_ == 0)
{
lean_dec_ref(v_stxStack_3457_);
lean_dec_ref(v_desc_3451_);
return v_s_3456_;
}
else
{
lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3461_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3457_);
lean_dec_ref(v_stxStack_3457_);
v___x_3462_ = l_Lean_Syntax_isOfKind(v___x_3461_, v_k_3450_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3456_, v_desc_3451_, v___x_3463_);
return v___x_3464_;
}
else
{
lean_dec_ref(v_desc_3451_);
return v_s_3456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3465_, lean_object* v_desc_3466_, lean_object* v_c_3467_, lean_object* v_s_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_Parser_expectTokenFn(v_k_3465_, v_desc_3466_, v_c_3467_, v_s_3468_);
lean_dec(v_k_3465_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3473_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3474_ = l_Lean_Parser_expectTokenFn(v___x_3472_, v___x_3473_, v_a_3470_, v_a_3471_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3476_ = l_Lean_Parser_mkAtomicInfo(v___x_3475_);
return v___x_3476_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3478_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3477_);
return v___x_3479_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3484_, lean_object* v_s_3485_){
_start:
{
lean_object* v_pos_3486_; uint8_t v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_pos_3486_ = lean_ctor_get(v_s_3485_, 2);
lean_inc(v_pos_3486_);
v___x_3487_ = 1;
v___x_3488_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3489_ = l_Lean_Parser_hexNumberFn(v_pos_3486_, v___x_3487_, v___x_3488_, v_ctx_3484_, v_s_3485_);
return v___x_3489_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3491_ = l_Lean_Parser_mkAtomicInfo(v___x_3490_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3493_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3492_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3500_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3501_ = l_Lean_Parser_expectTokenFn(v___x_3499_, v___x_3500_, v_a_3497_, v_a_3498_);
return v___x_3501_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3503_ = l_Lean_Parser_mkAtomicInfo(v___x_3502_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3505_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
lean_ctor_set(v___x_3506_, 1, v___x_3504_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3512_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3513_ = l_Lean_Parser_expectTokenFn(v___x_3511_, v___x_3512_, v_a_3509_, v_a_3510_);
return v___x_3513_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3515_ = l_Lean_Parser_mkAtomicInfo(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3517_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3524_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3525_ = l_Lean_Parser_expectTokenFn(v___x_3523_, v___x_3524_, v_a_3521_, v_a_3522_);
return v___x_3525_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3527_ = l_Lean_Parser_mkAtomicInfo(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3529_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3539_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3540_ = l_Lean_Parser_expectTokenFn(v___x_3538_, v___x_3539_, v_a_3536_, v_a_3537_);
return v___x_3540_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3542_ = l_Lean_Parser_mkAtomicInfo(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3544_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v___x_3543_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_c_3550_, lean_object* v_s_3551_){
_start:
{
lean_object* v_toCacheableParserContext_3552_; lean_object* v_forbiddenTks_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_toCacheableParserContext_3552_ = lean_ctor_get(v_c_3550_, 2);
v_forbiddenTks_3553_ = lean_ctor_get(v_toCacheableParserContext_3552_, 3);
v___x_3554_ = lean_array_get_size(v_forbiddenTks_3553_);
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = lean_nat_dec_eq(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v_pos_3557_; lean_object* v_iniSz_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v_s_3561_; lean_object* v_stxStack_3562_; lean_object* v_errorMsg_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
lean_inc_ref(v_forbiddenTks_3553_);
v_pos_3557_ = lean_ctor_get(v_s_3551_, 2);
lean_inc(v_pos_3557_);
v_iniSz_3558_ = l_Lean_Parser_ParserState_stackSize(v_s_3551_);
v___x_3559_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3560_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v_s_3561_ = l_Lean_Parser_expectTokenFn(v___x_3559_, v___x_3560_, v_c_3550_, v_s_3551_);
v_stxStack_3562_ = lean_ctor_get(v_s_3561_, 0);
lean_inc_ref(v_stxStack_3562_);
v_errorMsg_3563_ = lean_ctor_get(v_s_3561_, 4);
lean_inc(v_errorMsg_3563_);
v___x_3564_ = lean_box(0);
v___x_3565_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3563_, v___x_3564_);
lean_dec(v_errorMsg_3563_);
if (v___x_3565_ == 0)
{
lean_dec_ref(v_stxStack_3562_);
lean_dec(v_iniSz_3558_);
lean_dec(v_pos_3557_);
lean_dec_ref(v_forbiddenTks_3553_);
return v_s_3561_;
}
else
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3562_);
lean_dec_ref(v_stxStack_3562_);
if (lean_obj_tag(v___x_3566_) == 3)
{
lean_object* v_rawVal_3567_; lean_object* v_str_3568_; lean_object* v_startPos_3569_; lean_object* v_stopPos_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v_rawVal_3567_ = lean_ctor_get(v___x_3566_, 1);
lean_inc_ref(v_rawVal_3567_);
lean_dec_ref_known(v___x_3566_, 4);
v_str_3568_ = lean_ctor_get(v_rawVal_3567_, 0);
lean_inc_ref(v_str_3568_);
v_startPos_3569_ = lean_ctor_get(v_rawVal_3567_, 1);
lean_inc(v_startPos_3569_);
v_stopPos_3570_ = lean_ctor_get(v_rawVal_3567_, 2);
lean_inc(v_stopPos_3570_);
lean_dec_ref(v_rawVal_3567_);
v___x_3571_ = lean_string_utf8_extract(v_str_3568_, v_startPos_3569_, v_stopPos_3570_);
lean_dec(v_stopPos_3570_);
lean_dec(v_startPos_3569_);
lean_dec_ref(v_str_3568_);
v___x_3572_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_3553_, v___x_3571_);
lean_dec_ref(v___x_3571_);
lean_dec_ref(v_forbiddenTks_3553_);
if (v___x_3572_ == 0)
{
lean_dec(v_iniSz_3558_);
lean_dec(v_pos_3557_);
return v_s_3561_;
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3574_, 0, v_iniSz_3558_);
v___x_3575_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_3561_, v___x_3573_, v_pos_3557_, v___x_3574_);
lean_dec_ref_known(v___x_3574_, 1);
return v___x_3575_;
}
}
else
{
lean_dec(v___x_3566_);
lean_dec(v_iniSz_3558_);
lean_dec(v_pos_3557_);
lean_dec_ref(v_forbiddenTks_3553_);
return v_s_3561_;
}
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3577_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3578_ = l_Lean_Parser_expectTokenFn(v___x_3576_, v___x_3577_, v_c_3550_, v_s_3551_);
return v___x_3578_;
}
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3580_ = l_Lean_Parser_mkAtomicInfo(v___x_3579_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3582_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v___x_3581_);
return v___x_3583_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3596_, lean_object* v_c_3597_, lean_object* v_s_3598_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_s_3601_; lean_object* v_stxStack_3602_; lean_object* v_errorMsg_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3599_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3600_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3601_ = l_Lean_Parser_tokenFn(v___x_3600_, v_c_3597_, v_s_3598_);
v_stxStack_3602_ = lean_ctor_get(v_s_3601_, 0);
lean_inc_ref(v_stxStack_3602_);
v_errorMsg_3603_ = lean_ctor_get(v_s_3601_, 4);
lean_inc(v_errorMsg_3603_);
v___x_3604_ = lean_box(0);
v___x_3605_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3603_, v___x_3604_);
lean_dec(v_errorMsg_3603_);
if (v___x_3605_ == 0)
{
lean_dec_ref(v_stxStack_3602_);
lean_dec(v_id_3596_);
return v_s_3601_;
}
else
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3602_);
lean_dec_ref(v_stxStack_3602_);
if (lean_obj_tag(v___x_3606_) == 3)
{
lean_object* v_val_3607_; uint8_t v___x_3608_; 
v_val_3607_ = lean_ctor_get(v___x_3606_, 2);
lean_inc(v_val_3607_);
lean_dec_ref_known(v___x_3606_, 4);
v___x_3608_ = lean_name_eq(v_val_3607_, v_id_3596_);
lean_dec(v_val_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3609_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3596_, v___x_3605_);
v___x_3611_ = lean_string_append(v___x_3609_, v___x_3610_);
lean_dec_ref(v___x_3610_);
v___x_3612_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3613_ = lean_string_append(v___x_3611_, v___x_3612_);
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3601_, v___x_3613_, v___x_3614_);
return v___x_3615_;
}
else
{
lean_dec(v_id_3596_);
return v_s_3601_;
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_dec(v___x_3606_);
lean_dec(v_id_3596_);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3601_, v___x_3599_, v___x_3616_);
return v___x_3617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3618_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3620_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3620_, 0, v_id_3618_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3625_, lean_object* v_s_3626_){
_start:
{
lean_object* v_pos_3628_; lean_object* v_str_3629_; lean_object* v_trailing_3630_; lean_object* v_s_3631_; lean_object* v_stxStack_3643_; lean_object* v_pos_3644_; uint8_t v___x_3647_; 
v_stxStack_3643_ = lean_ctor_get(v_s_3626_, 0);
v_pos_3644_ = lean_ctor_get(v_s_3626_, 2);
v___x_3647_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3643_);
if (v___x_3647_ == 0)
{
lean_object* v_prev_3648_; lean_object* v___x_3649_; 
v_prev_3648_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3643_);
v___x_3649_ = l_Lean_Syntax_getTailInfo(v_prev_3648_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_leading_3650_; lean_object* v_pos_3651_; lean_object* v_trailing_3652_; lean_object* v_endPos_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3664_; 
v_leading_3650_ = lean_ctor_get(v___x_3649_, 0);
v_pos_3651_ = lean_ctor_get(v___x_3649_, 1);
v_trailing_3652_ = lean_ctor_get(v___x_3649_, 2);
v_endPos_3653_ = lean_ctor_get(v___x_3649_, 3);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3655_ = v___x_3649_;
v_isShared_3656_ = v_isSharedCheck_3664_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_endPos_3653_);
lean_inc(v_trailing_3652_);
lean_inc(v_pos_3651_);
lean_inc(v_leading_3650_);
lean_dec(v___x_3649_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3664_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v_str_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_inc_n(v_endPos_3653_, 2);
v_str_3657_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3625_, v_endPos_3653_);
v___x_3658_ = l_Lean_Parser_ParserState_popSyntax(v_s_3626_);
lean_inc_ref(v_str_3657_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 2, v_str_3657_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_leading_3650_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_pos_3651_);
lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_str_3657_);
lean_ctor_set(v_reuseFailAlloc_3663_, 3, v_endPos_3653_);
v___x_3660_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v_s_3662_; 
v___x_3661_ = l_Lean_Syntax_setTailInfo(v_prev_3648_, v___x_3660_);
v_s_3662_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3658_, v___x_3661_);
v_pos_3628_ = v_endPos_3653_;
v_str_3629_ = v_str_3657_;
v_trailing_3630_ = v_trailing_3652_;
v_s_3631_ = v_s_3662_;
goto v___jp_3627_;
}
}
}
else
{
lean_inc(v_pos_3644_);
lean_dec(v___x_3649_);
lean_dec(v_prev_3648_);
goto v___jp_3645_;
}
}
else
{
lean_inc(v_pos_3644_);
goto v___jp_3645_;
}
v___jp_3627_:
{
lean_object* v_info_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v_ident_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_inc(v_pos_3628_);
lean_inc_ref(v_str_3629_);
v_info_3632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3632_, 0, v_str_3629_);
lean_ctor_set(v_info_3632_, 1, v_pos_3628_);
lean_ctor_set(v_info_3632_, 2, v_trailing_3630_);
lean_ctor_set(v_info_3632_, 3, v_pos_3628_);
v___x_3633_ = lean_box(0);
v___x_3634_ = lean_box(0);
v_ident_3635_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3635_, 0, v_info_3632_);
lean_ctor_set(v_ident_3635_, 1, v_str_3629_);
lean_ctor_set(v_ident_3635_, 2, v___x_3633_);
lean_ctor_set(v_ident_3635_, 3, v___x_3634_);
v___x_3636_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3637_ = lean_unsigned_to_nat(1u);
v___x_3638_ = lean_mk_empty_array_with_capacity(v___x_3637_);
v___x_3639_ = lean_array_push(v___x_3638_, v_ident_3635_);
v___x_3640_ = lean_box(2);
v___x_3641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v___x_3636_);
lean_ctor_set(v___x_3641_, 2, v___x_3639_);
v___x_3642_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3631_, v___x_3641_);
return v___x_3642_;
}
v___jp_3645_:
{
lean_object* v_str_3646_; 
lean_inc(v_pos_3644_);
v_str_3646_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3625_, v_pos_3644_);
lean_inc_ref(v_str_3646_);
v_pos_3628_ = v_pos_3644_;
v_str_3629_ = v_str_3646_;
v_trailing_3630_ = v_str_3646_;
v_s_3631_ = v_s_3626_;
goto v___jp_3627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3665_, lean_object* v_s_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Parser_hygieneInfoFn(v_c_3665_, v_s_3666_);
lean_dec_ref(v_c_3665_);
return v_res_3667_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3669_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3670_ = l_Lean_Parser_nodeInfo(v___x_3669_, v___x_3668_);
return v___x_3670_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3672_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v___x_3671_);
return v___x_3673_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3675_, lean_object* v_startStackSize_3676_){
_start:
{
lean_object* v_node_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v_node_3677_ = l_Lean_Parser_SyntaxStack_back(v_s_3675_);
v___x_3678_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3675_, v_startStackSize_3676_);
v___x_3679_ = l_Lean_Parser_SyntaxStack_push(v___x_3678_, v_node_3677_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3680_, lean_object* v_startStackSize_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Parser_ParserState_keepTop(v_s_3680_, v_startStackSize_3681_);
lean_dec(v_startStackSize_3681_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3683_, lean_object* v_oldStackSize_3684_){
_start:
{
lean_object* v_stxStack_3685_; lean_object* v_lhsPrec_3686_; lean_object* v_pos_3687_; lean_object* v_cache_3688_; lean_object* v_errorMsg_3689_; lean_object* v_recoveredErrors_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3698_; 
v_stxStack_3685_ = lean_ctor_get(v_s_3683_, 0);
v_lhsPrec_3686_ = lean_ctor_get(v_s_3683_, 1);
v_pos_3687_ = lean_ctor_get(v_s_3683_, 2);
v_cache_3688_ = lean_ctor_get(v_s_3683_, 3);
v_errorMsg_3689_ = lean_ctor_get(v_s_3683_, 4);
v_recoveredErrors_3690_ = lean_ctor_get(v_s_3683_, 5);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_s_3683_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3692_ = v_s_3683_;
v_isShared_3693_ = v_isSharedCheck_3698_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_recoveredErrors_3690_);
lean_inc(v_errorMsg_3689_);
lean_inc(v_cache_3688_);
lean_inc(v_pos_3687_);
lean_inc(v_lhsPrec_3686_);
lean_inc(v_stxStack_3685_);
lean_dec(v_s_3683_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3698_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3694_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3685_, v_oldStackSize_3684_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3694_);
v___x_3696_ = v___x_3692_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_lhsPrec_3686_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_pos_3687_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_cache_3688_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_errorMsg_3689_);
lean_ctor_set(v_reuseFailAlloc_3697_, 5, v_recoveredErrors_3690_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3699_, lean_object* v_oldStackSize_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Parser_ParserState_keepNewError(v_s_3699_, v_oldStackSize_3700_);
lean_dec(v_oldStackSize_3700_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3702_, lean_object* v_oldStackSize_3703_, lean_object* v_oldStopPos_3704_, lean_object* v_oldError_3705_, lean_object* v_oldLhsPrec_3706_){
_start:
{
lean_object* v_stxStack_3707_; lean_object* v_cache_3708_; lean_object* v_recoveredErrors_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3717_; 
v_stxStack_3707_ = lean_ctor_get(v_s_3702_, 0);
v_cache_3708_ = lean_ctor_get(v_s_3702_, 3);
v_recoveredErrors_3709_ = lean_ctor_get(v_s_3702_, 5);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_s_3702_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; lean_object* v_unused_3719_; lean_object* v_unused_3720_; 
v_unused_3718_ = lean_ctor_get(v_s_3702_, 4);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_s_3702_, 2);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_s_3702_, 1);
lean_dec(v_unused_3720_);
v___x_3711_ = v_s_3702_;
v_isShared_3712_ = v_isSharedCheck_3717_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_recoveredErrors_3709_);
lean_inc(v_cache_3708_);
lean_inc(v_stxStack_3707_);
lean_dec(v_s_3702_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3717_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3713_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3707_, v_oldStackSize_3703_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 4, v_oldError_3705_);
lean_ctor_set(v___x_3711_, 2, v_oldStopPos_3704_);
lean_ctor_set(v___x_3711_, 1, v_oldLhsPrec_3706_);
lean_ctor_set(v___x_3711_, 0, v___x_3713_);
v___x_3715_ = v___x_3711_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_oldLhsPrec_3706_);
lean_ctor_set(v_reuseFailAlloc_3716_, 2, v_oldStopPos_3704_);
lean_ctor_set(v_reuseFailAlloc_3716_, 3, v_cache_3708_);
lean_ctor_set(v_reuseFailAlloc_3716_, 4, v_oldError_3705_);
lean_ctor_set(v_reuseFailAlloc_3716_, 5, v_recoveredErrors_3709_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3721_, lean_object* v_oldStackSize_3722_, lean_object* v_oldStopPos_3723_, lean_object* v_oldError_3724_, lean_object* v_oldLhsPrec_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3721_, v_oldStackSize_3722_, v_oldStopPos_3723_, v_oldError_3724_, v_oldLhsPrec_3725_);
lean_dec(v_oldStackSize_3722_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3727_, lean_object* v_oldStackSize_3728_, lean_object* v_oldError_3729_){
_start:
{
lean_object* v_stxStack_3730_; lean_object* v_lhsPrec_3731_; lean_object* v_pos_3732_; lean_object* v_cache_3733_; lean_object* v_errorMsg_3734_; lean_object* v_recoveredErrors_3735_; lean_object* v___y_3737_; 
v_stxStack_3730_ = lean_ctor_get(v_s_3727_, 0);
v_lhsPrec_3731_ = lean_ctor_get(v_s_3727_, 1);
v_pos_3732_ = lean_ctor_get(v_s_3727_, 2);
v_cache_3733_ = lean_ctor_get(v_s_3727_, 3);
v_errorMsg_3734_ = lean_ctor_get(v_s_3727_, 4);
v_recoveredErrors_3735_ = lean_ctor_get(v_s_3727_, 5);
if (lean_obj_tag(v_errorMsg_3734_) == 1)
{
lean_object* v_val_3741_; uint8_t v___x_3742_; 
lean_inc_ref(v_errorMsg_3734_);
lean_inc_ref(v_recoveredErrors_3735_);
lean_inc_ref(v_cache_3733_);
lean_inc(v_pos_3732_);
lean_inc(v_lhsPrec_3731_);
lean_inc_ref(v_stxStack_3730_);
lean_dec_ref(v_s_3727_);
v_val_3741_ = lean_ctor_get(v_errorMsg_3734_, 0);
lean_inc(v_val_3741_);
lean_dec_ref_known(v_errorMsg_3734_, 1);
v___x_3742_ = l_Lean_Parser_instBEqError_beq(v_oldError_3729_, v_val_3741_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Parser_Error_merge(v_oldError_3729_, v_val_3741_);
v___y_3737_ = v___x_3743_;
goto v___jp_3736_;
}
else
{
lean_dec_ref(v_oldError_3729_);
v___y_3737_ = v_val_3741_;
goto v___jp_3736_;
}
}
else
{
lean_dec_ref(v_oldError_3729_);
return v_s_3727_;
}
v___jp_3736_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3730_, v_oldStackSize_3728_);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___y_3737_);
v___x_3740_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v_lhsPrec_3731_);
lean_ctor_set(v___x_3740_, 2, v_pos_3732_);
lean_ctor_set(v___x_3740_, 3, v_cache_3733_);
lean_ctor_set(v___x_3740_, 4, v___x_3739_);
lean_ctor_set(v___x_3740_, 5, v_recoveredErrors_3735_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3744_, lean_object* v_oldStackSize_3745_, lean_object* v_oldError_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3744_, v_oldStackSize_3745_, v_oldError_3746_);
lean_dec(v_oldStackSize_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3748_, lean_object* v_startStackSize_3749_){
_start:
{
lean_object* v_stxStack_3750_; lean_object* v_lhsPrec_3751_; lean_object* v_pos_3752_; lean_object* v_cache_3753_; lean_object* v_recoveredErrors_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3763_; 
v_stxStack_3750_ = lean_ctor_get(v_s_3748_, 0);
v_lhsPrec_3751_ = lean_ctor_get(v_s_3748_, 1);
v_pos_3752_ = lean_ctor_get(v_s_3748_, 2);
v_cache_3753_ = lean_ctor_get(v_s_3748_, 3);
v_recoveredErrors_3754_ = lean_ctor_get(v_s_3748_, 5);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_s_3748_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v_s_3748_, 4);
lean_dec(v_unused_3764_);
v___x_3756_ = v_s_3748_;
v_isShared_3757_ = v_isSharedCheck_3763_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_recoveredErrors_3754_);
lean_inc(v_cache_3753_);
lean_inc(v_pos_3752_);
lean_inc(v_lhsPrec_3751_);
lean_inc(v_stxStack_3750_);
lean_dec(v_s_3748_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3763_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
v___x_3758_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3750_, v_startStackSize_3749_);
v___x_3759_ = lean_box(0);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 4, v___x_3759_);
lean_ctor_set(v___x_3756_, 0, v___x_3758_);
v___x_3761_ = v___x_3756_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_lhsPrec_3751_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_pos_3752_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_cache_3753_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3762_, 5, v_recoveredErrors_3754_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3765_, lean_object* v_startStackSize_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Parser_ParserState_keepLatest(v_s_3765_, v_startStackSize_3766_);
lean_dec(v_startStackSize_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3768_, lean_object* v_startStackSize_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_Parser_ParserState_keepLatest(v_s_3768_, v_startStackSize_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3771_, lean_object* v_startStackSize_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3771_, v_startStackSize_3772_);
lean_dec(v_startStackSize_3772_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3775_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3777_ = l_Lean_Parser_ParserState_mkError(v_s_3775_, v___x_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3778_, lean_object* v_startLhsPrec_3779_, lean_object* v_p_3780_, lean_object* v_c_3781_, lean_object* v_s_3782_){
_start:
{
lean_object* v___y_3784_; lean_object* v_s_3785_; lean_object* v_stxStack_3798_; lean_object* v_pos_3799_; lean_object* v_cache_3800_; lean_object* v_errorMsg_3801_; lean_object* v_recoveredErrors_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3815_; 
v_stxStack_3798_ = lean_ctor_get(v_s_3782_, 0);
v_pos_3799_ = lean_ctor_get(v_s_3782_, 2);
v_cache_3800_ = lean_ctor_get(v_s_3782_, 3);
v_errorMsg_3801_ = lean_ctor_get(v_s_3782_, 4);
v_recoveredErrors_3802_ = lean_ctor_get(v_s_3782_, 5);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_s_3782_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v_s_3782_, 1);
lean_dec(v_unused_3816_);
v___x_3804_ = v_s_3782_;
v_isShared_3805_ = v_isSharedCheck_3815_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_recoveredErrors_3802_);
lean_inc(v_errorMsg_3801_);
lean_inc(v_cache_3800_);
lean_inc(v_pos_3799_);
lean_inc(v_stxStack_3798_);
lean_dec(v_s_3782_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3815_;
goto v_resetjp_3803_;
}
v___jp_3783_:
{
lean_object* v_s_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_s_3786_ = lean_apply_2(v_p_3780_, v_c_3781_, v_s_3785_);
v___x_3787_ = l_Lean_Parser_ParserState_stackSize(v_s_3786_);
v___x_3788_ = lean_unsigned_to_nat(1u);
v___x_3789_ = lean_nat_add(v___y_3784_, v___x_3788_);
v___x_3790_ = lean_nat_dec_eq(v___x_3787_, v___x_3789_);
lean_dec(v___x_3789_);
lean_dec(v___x_3787_);
if (v___x_3790_ == 0)
{
lean_object* v_errorMsg_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v_errorMsg_3791_ = lean_ctor_get(v_s_3786_, 4);
lean_inc(v_errorMsg_3791_);
v___x_3792_ = lean_box(0);
v___x_3793_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3791_, v___x_3792_);
lean_dec(v_errorMsg_3791_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3786_, v___y_3784_);
lean_dec(v___y_3784_);
v___x_3795_ = lean_box(0);
v___x_3796_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3794_, v___x_3795_);
return v___x_3796_;
}
else
{
lean_object* v___x_3797_; 
lean_dec(v___y_3784_);
v___x_3797_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3786_);
return v___x_3797_;
}
}
else
{
lean_dec(v___y_3784_);
return v_s_3786_;
}
}
v_resetjp_3803_:
{
lean_object* v___y_3807_; 
if (lean_obj_tag(v_left_x3f_3778_) == 0)
{
lean_object* v___x_3814_; 
lean_dec(v_startLhsPrec_3779_);
v___x_3814_ = l_Lean_Parser_maxPrec;
v___y_3807_ = v___x_3814_;
goto v___jp_3806_;
}
else
{
v___y_3807_ = v_startLhsPrec_3779_;
goto v___jp_3806_;
}
v___jp_3806_:
{
lean_object* v_s_3809_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v___y_3807_);
v_s_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_stxStack_3798_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___y_3807_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_pos_3799_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_cache_3800_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_errorMsg_3801_);
lean_ctor_set(v_reuseFailAlloc_3813_, 5, v_recoveredErrors_3802_);
v_s_3809_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v_startSize_3810_; 
v_startSize_3810_ = l_Lean_Parser_ParserState_stackSize(v_s_3809_);
if (lean_obj_tag(v_left_x3f_3778_) == 1)
{
lean_object* v_val_3811_; lean_object* v_s_3812_; 
v_val_3811_ = lean_ctor_get(v_left_x3f_3778_, 0);
lean_inc(v_val_3811_);
lean_dec_ref_known(v_left_x3f_3778_, 1);
v_s_3812_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3809_, v_val_3811_);
v___y_3784_ = v_startSize_3810_;
v_s_3785_ = v_s_3812_;
goto v___jp_3783_;
}
else
{
lean_dec(v_left_x3f_3778_);
v___y_3784_ = v_startSize_3810_;
v_s_3785_ = v_s_3809_;
goto v___jp_3783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3817_, lean_object* v_prio_3818_){
_start:
{
lean_object* v_pos_3819_; lean_object* v_errorMsg_3820_; lean_object* v___y_3822_; 
v_pos_3819_ = lean_ctor_get(v_s_3817_, 2);
v_errorMsg_3820_ = lean_ctor_get(v_s_3817_, 4);
if (lean_obj_tag(v_errorMsg_3820_) == 0)
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_unsigned_to_nat(1u);
v___y_3822_ = v___x_3825_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_unsigned_to_nat(0u);
v___y_3822_ = v___x_3826_;
goto v___jp_3821_;
}
v___jp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___y_3822_);
lean_ctor_set(v___x_3823_, 1, v_prio_3818_);
lean_inc(v_pos_3819_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v_pos_3819_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
return v___x_3824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3827_, lean_object* v_prio_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3827_, v_prio_3828_);
lean_dec_ref(v_s_3827_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3830_, lean_object* v_startSize_3831_, lean_object* v_startLhsPrec_3832_, lean_object* v_startPos_3833_, lean_object* v_prevPrio_3834_, lean_object* v_prio_3835_, lean_object* v_p_3836_, lean_object* v_c_3837_, lean_object* v_s_3838_){
_start:
{
lean_object* v_lhsPrec_3839_; lean_object* v_pos_3840_; lean_object* v_errorMsg_3841_; lean_object* v_previousScore_3842_; lean_object* v_fst_3843_; lean_object* v_snd_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3900_; 
v_lhsPrec_3839_ = lean_ctor_get(v_s_3838_, 1);
lean_inc(v_lhsPrec_3839_);
v_pos_3840_ = lean_ctor_get(v_s_3838_, 2);
lean_inc(v_pos_3840_);
v_errorMsg_3841_ = lean_ctor_get(v_s_3838_, 4);
lean_inc(v_errorMsg_3841_);
lean_inc(v_prevPrio_3834_);
v_previousScore_3842_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3838_, v_prevPrio_3834_);
v_fst_3843_ = lean_ctor_get(v_previousScore_3842_, 0);
v_snd_3844_ = lean_ctor_get(v_previousScore_3842_, 1);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_previousScore_3842_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3846_ = v_previousScore_3842_;
v_isShared_3847_ = v_isSharedCheck_3900_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_snd_3844_);
lean_inc(v_fst_3843_);
lean_dec(v_previousScore_3842_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3900_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_prevSize_3848_; lean_object* v_s_3849_; lean_object* v_s_3850_; lean_object* v___x_3859_; lean_object* v_fst_3860_; lean_object* v_snd_3861_; uint8_t v___x_3862_; 
v_prevSize_3848_ = l_Lean_Parser_ParserState_stackSize(v_s_3838_);
v_s_3849_ = l_Lean_Parser_ParserState_restore(v_s_3838_, v_prevSize_3848_, v_startPos_3833_);
v_s_3850_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3830_, v_startLhsPrec_3832_, v_p_3836_, v_c_3837_, v_s_3849_);
lean_inc(v_prio_3835_);
v___x_3859_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3850_, v_prio_3835_);
v_fst_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_fst_3860_);
v_snd_3861_ = lean_ctor_get(v___x_3859_, 1);
lean_inc(v_snd_3861_);
lean_dec_ref(v___x_3859_);
v___x_3862_ = lean_nat_dec_lt(v_fst_3843_, v_fst_3860_);
if (v___x_3862_ == 0)
{
uint8_t v___x_3863_; 
v___x_3863_ = lean_nat_dec_eq(v_fst_3843_, v_fst_3860_);
lean_dec(v_fst_3860_);
lean_dec(v_fst_3843_);
if (v___x_3863_ == 0)
{
lean_dec(v_snd_3861_);
lean_del_object(v___x_3846_);
lean_dec(v_snd_3844_);
lean_dec(v_prio_3835_);
goto v___jp_3856_;
}
else
{
lean_object* v_fst_3864_; lean_object* v_snd_3865_; lean_object* v_fst_3866_; lean_object* v_snd_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3899_; 
v_fst_3864_ = lean_ctor_get(v_snd_3844_, 0);
lean_inc(v_fst_3864_);
v_snd_3865_ = lean_ctor_get(v_snd_3844_, 1);
lean_inc(v_snd_3865_);
lean_dec(v_snd_3844_);
v_fst_3866_ = lean_ctor_get(v_snd_3861_, 0);
v_snd_3867_ = lean_ctor_get(v_snd_3861_, 1);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_snd_3861_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3869_ = v_snd_3861_;
v_isShared_3870_ = v_isSharedCheck_3899_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_snd_3867_);
lean_inc(v_fst_3866_);
lean_dec(v_snd_3861_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3899_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
uint8_t v___x_3871_; 
v___x_3871_ = lean_nat_dec_lt(v_fst_3864_, v_fst_3866_);
if (v___x_3871_ == 0)
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_nat_dec_eq(v_fst_3864_, v_fst_3866_);
lean_dec(v_fst_3866_);
lean_dec(v_fst_3864_);
if (v___x_3872_ == 0)
{
lean_del_object(v___x_3869_);
lean_dec(v_snd_3867_);
lean_dec(v_snd_3865_);
lean_del_object(v___x_3846_);
lean_dec(v_prio_3835_);
goto v___jp_3856_;
}
else
{
uint8_t v___x_3873_; 
v___x_3873_ = lean_nat_dec_lt(v_snd_3865_, v_snd_3867_);
if (v___x_3873_ == 0)
{
uint8_t v___x_3874_; 
lean_del_object(v___x_3846_);
v___x_3874_ = lean_nat_dec_eq(v_snd_3865_, v_snd_3867_);
lean_dec(v_snd_3867_);
lean_dec(v_snd_3865_);
if (v___x_3874_ == 0)
{
lean_del_object(v___x_3869_);
lean_dec(v_prio_3835_);
goto v___jp_3856_;
}
else
{
lean_dec(v_pos_3840_);
lean_dec(v_prevPrio_3834_);
if (lean_obj_tag(v_errorMsg_3841_) == 0)
{
lean_object* v_stxStack_3875_; lean_object* v_lhsPrec_3876_; lean_object* v_pos_3877_; lean_object* v_cache_3878_; lean_object* v_errorMsg_3879_; lean_object* v_recoveredErrors_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3893_; 
lean_dec(v_prevSize_3848_);
v_stxStack_3875_ = lean_ctor_get(v_s_3850_, 0);
v_lhsPrec_3876_ = lean_ctor_get(v_s_3850_, 1);
v_pos_3877_ = lean_ctor_get(v_s_3850_, 2);
v_cache_3878_ = lean_ctor_get(v_s_3850_, 3);
v_errorMsg_3879_ = lean_ctor_get(v_s_3850_, 4);
v_recoveredErrors_3880_ = lean_ctor_get(v_s_3850_, 5);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_s_3850_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3882_ = v_s_3850_;
v_isShared_3883_ = v_isSharedCheck_3893_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_recoveredErrors_3880_);
lean_inc(v_errorMsg_3879_);
lean_inc(v_cache_3878_);
lean_inc(v_pos_3877_);
lean_inc(v_lhsPrec_3876_);
lean_inc(v_stxStack_3875_);
lean_dec(v_s_3850_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3893_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___y_3885_; uint8_t v___x_3892_; 
v___x_3892_ = lean_nat_dec_le(v_lhsPrec_3876_, v_lhsPrec_3839_);
if (v___x_3892_ == 0)
{
lean_dec(v_lhsPrec_3876_);
v___y_3885_ = v_lhsPrec_3839_;
goto v___jp_3884_;
}
else
{
lean_dec(v_lhsPrec_3839_);
v___y_3885_ = v_lhsPrec_3876_;
goto v___jp_3884_;
}
v___jp_3884_:
{
lean_object* v___x_3887_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___y_3885_);
v___x_3887_ = v___x_3882_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_stxStack_3875_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v___y_3885_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_pos_3877_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_cache_3878_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v_errorMsg_3879_);
lean_ctor_set(v_reuseFailAlloc_3891_, 5, v_recoveredErrors_3880_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 1, v_prio_3835_);
lean_ctor_set(v___x_3869_, 0, v___x_3887_);
v___x_3889_ = v___x_3869_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_prio_3835_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
lean_dec(v_lhsPrec_3839_);
v_val_3894_ = lean_ctor_get(v_errorMsg_3841_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v_errorMsg_3841_, 1);
v___x_3895_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3850_, v_prevSize_3848_, v_val_3894_);
lean_dec(v_prevSize_3848_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 1, v_prio_3835_);
lean_ctor_set(v___x_3869_, 0, v___x_3895_);
v___x_3897_ = v___x_3869_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_prio_3835_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_del_object(v___x_3869_);
lean_dec(v_snd_3867_);
lean_dec(v_snd_3865_);
lean_dec(v_prevSize_3848_);
lean_dec(v_errorMsg_3841_);
lean_dec(v_pos_3840_);
lean_dec(v_lhsPrec_3839_);
lean_dec(v_prevPrio_3834_);
goto v___jp_3851_;
}
}
}
else
{
lean_del_object(v___x_3869_);
lean_dec(v_snd_3867_);
lean_dec(v_fst_3866_);
lean_dec(v_snd_3865_);
lean_dec(v_fst_3864_);
lean_dec(v_prevSize_3848_);
lean_dec(v_errorMsg_3841_);
lean_dec(v_pos_3840_);
lean_dec(v_lhsPrec_3839_);
lean_dec(v_prevPrio_3834_);
goto v___jp_3851_;
}
}
}
}
else
{
lean_dec(v_snd_3861_);
lean_dec(v_fst_3860_);
lean_dec(v_prevSize_3848_);
lean_dec(v_snd_3844_);
lean_dec(v_fst_3843_);
lean_dec(v_errorMsg_3841_);
lean_dec(v_pos_3840_);
lean_dec(v_lhsPrec_3839_);
lean_dec(v_prevPrio_3834_);
goto v___jp_3851_;
}
v___jp_3851_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = l_Lean_Parser_ParserState_keepNewError(v_s_3850_, v_startSize_3831_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 1, v_prio_3835_);
lean_ctor_set(v___x_3846_, 0, v___x_3852_);
v___x_3854_ = v___x_3846_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_prio_3835_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
v___jp_3856_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3850_, v_prevSize_3848_, v_pos_3840_, v_errorMsg_3841_, v_lhsPrec_3839_);
lean_dec(v_prevSize_3848_);
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
lean_ctor_set(v___x_3858_, 1, v_prevPrio_3834_);
return v___x_3858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3901_, lean_object* v_startSize_3902_, lean_object* v_startLhsPrec_3903_, lean_object* v_startPos_3904_, lean_object* v_prevPrio_3905_, lean_object* v_prio_3906_, lean_object* v_p_3907_, lean_object* v_c_3908_, lean_object* v_s_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3901_, v_startSize_3902_, v_startLhsPrec_3903_, v_startPos_3904_, v_prevPrio_3905_, v_prio_3906_, v_p_3907_, v_c_3908_, v_s_3909_);
lean_dec(v_startSize_3902_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3911_, lean_object* v_s_3912_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3913_ = lean_unsigned_to_nat(1u);
v___x_3914_ = lean_nat_add(v_startSize_3911_, v___x_3913_);
v___x_3915_ = l_Lean_Parser_ParserState_stackSize(v_s_3912_);
v___x_3916_ = lean_nat_dec_lt(v___x_3914_, v___x_3915_);
lean_dec(v___x_3915_);
lean_dec(v___x_3914_);
if (v___x_3916_ == 0)
{
return v_s_3912_;
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3918_ = l_Lean_Parser_ParserState_mkNode(v_s_3912_, v___x_3917_, v_startSize_3911_);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3919_, lean_object* v_s_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3919_, v_s_3920_);
lean_dec(v_startSize_3919_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3922_, lean_object* v_startSize_3923_, lean_object* v_startLhsPrec_3924_, lean_object* v_startPos_3925_, lean_object* v_prevPrio_3926_, lean_object* v_ps_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
if (lean_obj_tag(v_ps_3927_) == 0)
{
lean_object* v___x_3930_; 
lean_dec_ref(v_a_3928_);
lean_dec(v_prevPrio_3926_);
lean_dec(v_startPos_3925_);
lean_dec(v_startLhsPrec_3924_);
lean_dec(v_left_x3f_3922_);
v___x_3930_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3923_, v_a_3929_);
return v___x_3930_;
}
else
{
lean_object* v_head_3931_; lean_object* v_fst_3932_; lean_object* v_tail_3933_; lean_object* v_snd_3934_; lean_object* v_fn_3935_; lean_object* v___x_3936_; lean_object* v_fst_3937_; lean_object* v_snd_3938_; 
v_head_3931_ = lean_ctor_get(v_ps_3927_, 0);
lean_inc(v_head_3931_);
v_fst_3932_ = lean_ctor_get(v_head_3931_, 0);
lean_inc(v_fst_3932_);
v_tail_3933_ = lean_ctor_get(v_ps_3927_, 1);
lean_inc(v_tail_3933_);
lean_dec_ref_known(v_ps_3927_, 2);
v_snd_3934_ = lean_ctor_get(v_head_3931_, 1);
lean_inc(v_snd_3934_);
lean_dec(v_head_3931_);
v_fn_3935_ = lean_ctor_get(v_fst_3932_, 1);
lean_inc_ref(v_fn_3935_);
lean_dec(v_fst_3932_);
lean_inc_ref(v_a_3928_);
lean_inc(v_startPos_3925_);
lean_inc(v_startLhsPrec_3924_);
lean_inc(v_left_x3f_3922_);
v___x_3936_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3922_, v_startSize_3923_, v_startLhsPrec_3924_, v_startPos_3925_, v_prevPrio_3926_, v_snd_3934_, v_fn_3935_, v_a_3928_, v_a_3929_);
v_fst_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_fst_3937_);
v_snd_3938_ = lean_ctor_get(v___x_3936_, 1);
lean_inc(v_snd_3938_);
lean_dec_ref(v___x_3936_);
v_prevPrio_3926_ = v_snd_3938_;
v_ps_3927_ = v_tail_3933_;
v_a_3929_ = v_fst_3937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3940_, lean_object* v_startSize_3941_, lean_object* v_startLhsPrec_3942_, lean_object* v_startPos_3943_, lean_object* v_prevPrio_3944_, lean_object* v_ps_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3940_, v_startSize_3941_, v_startLhsPrec_3942_, v_startPos_3943_, v_prevPrio_3944_, v_ps_3945_, v_a_3946_, v_a_3947_);
lean_dec(v_startSize_3941_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3949_, lean_object* v_startSize_3950_, lean_object* v_startLhsPrec_3951_, lean_object* v_startPos_3952_, lean_object* v_prevPrio_3953_, lean_object* v_ps_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3949_, v_startSize_3950_, v_startLhsPrec_3951_, v_startPos_3952_, v_prevPrio_3953_, v_ps_3954_, v_a_3955_, v_a_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3958_, lean_object* v_startSize_3959_, lean_object* v_startLhsPrec_3960_, lean_object* v_startPos_3961_, lean_object* v_prevPrio_3962_, lean_object* v_ps_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3958_, v_startSize_3959_, v_startLhsPrec_3960_, v_startPos_3961_, v_prevPrio_3962_, v_ps_3963_, v_a_3964_, v_a_3965_);
lean_dec(v_startSize_3959_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3968_, lean_object* v_x_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 0)
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_dec_ref(v_a_3970_);
lean_dec(v_left_x3f_3968_);
v___x_3972_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3973_ = l_Lean_Parser_ParserState_mkError(v_a_3971_, v___x_3972_);
return v___x_3973_;
}
else
{
lean_object* v_tail_3974_; 
v_tail_3974_ = lean_ctor_get(v_x_3969_, 1);
if (lean_obj_tag(v_tail_3974_) == 0)
{
lean_object* v_head_3975_; lean_object* v_fst_3976_; lean_object* v_lhsPrec_3977_; lean_object* v_fn_3978_; lean_object* v___x_3979_; 
v_head_3975_ = lean_ctor_get(v_x_3969_, 0);
lean_inc(v_head_3975_);
lean_dec_ref_known(v_x_3969_, 2);
v_fst_3976_ = lean_ctor_get(v_head_3975_, 0);
lean_inc(v_fst_3976_);
lean_dec(v_head_3975_);
v_lhsPrec_3977_ = lean_ctor_get(v_a_3971_, 1);
lean_inc(v_lhsPrec_3977_);
v_fn_3978_ = lean_ctor_get(v_fst_3976_, 1);
lean_inc_ref(v_fn_3978_);
lean_dec(v_fst_3976_);
v___x_3979_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3968_, v_lhsPrec_3977_, v_fn_3978_, v_a_3970_, v_a_3971_);
return v___x_3979_;
}
else
{
lean_object* v_head_3980_; lean_object* v_fst_3981_; lean_object* v_lhsPrec_3982_; lean_object* v_pos_3983_; lean_object* v_snd_3984_; lean_object* v_fn_3985_; lean_object* v_startSize_3986_; lean_object* v_s_3987_; lean_object* v___x_3988_; 
lean_inc(v_tail_3974_);
v_head_3980_ = lean_ctor_get(v_x_3969_, 0);
lean_inc(v_head_3980_);
lean_dec_ref_known(v_x_3969_, 2);
v_fst_3981_ = lean_ctor_get(v_head_3980_, 0);
lean_inc(v_fst_3981_);
v_lhsPrec_3982_ = lean_ctor_get(v_a_3971_, 1);
lean_inc_n(v_lhsPrec_3982_, 2);
v_pos_3983_ = lean_ctor_get(v_a_3971_, 2);
lean_inc(v_pos_3983_);
v_snd_3984_ = lean_ctor_get(v_head_3980_, 1);
lean_inc(v_snd_3984_);
lean_dec(v_head_3980_);
v_fn_3985_ = lean_ctor_get(v_fst_3981_, 1);
lean_inc_ref(v_fn_3985_);
lean_dec(v_fst_3981_);
v_startSize_3986_ = l_Lean_Parser_ParserState_stackSize(v_a_3971_);
lean_inc_ref(v_a_3970_);
lean_inc(v_left_x3f_3968_);
v_s_3987_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3968_, v_lhsPrec_3982_, v_fn_3985_, v_a_3970_, v_a_3971_);
v___x_3988_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3968_, v_startSize_3986_, v_lhsPrec_3982_, v_pos_3983_, v_snd_3984_, v_tail_3974_, v_a_3970_, v_s_3987_);
lean_dec(v_startSize_3986_);
return v___x_3988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
if (lean_obj_tag(v_x_3990_) == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_x_3991_);
v___x_3993_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_3994_ = l_Lean_Parser_ParserState_mkError(v_x_3992_, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v_tail_3995_; 
v_tail_3995_ = lean_ctor_get(v_x_3990_, 1);
if (lean_obj_tag(v_tail_3995_) == 0)
{
lean_object* v_head_3996_; lean_object* v_fn_3997_; lean_object* v___x_3998_; 
v_head_3996_ = lean_ctor_get(v_x_3990_, 0);
lean_inc(v_head_3996_);
lean_dec_ref_known(v_x_3990_, 2);
v_fn_3997_ = lean_ctor_get(v_head_3996_, 1);
lean_inc_ref(v_fn_3997_);
lean_dec(v_head_3996_);
v___x_3998_ = lean_apply_2(v_fn_3997_, v_x_3991_, v_x_3992_);
return v___x_3998_;
}
else
{
lean_object* v_head_3999_; lean_object* v_fn_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
lean_inc(v_tail_3995_);
v_head_3999_ = lean_ctor_get(v_x_3990_, 0);
lean_inc(v_head_3999_);
lean_dec_ref_known(v_x_3990_, 2);
v_fn_4000_ = lean_ctor_get(v_head_3999_, 1);
lean_inc_ref(v_fn_4000_);
lean_dec(v_head_3999_);
v___x_4001_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_4001_, 0, v_tail_3995_);
v___x_4002_ = l_Lean_Parser_orelseFn(v_fn_4000_, v___x_4001_, v_x_3991_, v_x_3992_);
return v___x_4002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_4003_, lean_object* v_c_4004_, lean_object* v_s_4005_){
_start:
{
lean_object* v_toCacheableParserContext_4006_; lean_object* v_savedPos_x3f_4007_; 
v_toCacheableParserContext_4006_ = lean_ctor_get(v_c_4004_, 2);
v_savedPos_x3f_4007_ = lean_ctor_get(v_toCacheableParserContext_4006_, 2);
lean_inc(v_savedPos_x3f_4007_);
if (lean_obj_tag(v_savedPos_x3f_4007_) == 0)
{
lean_dec_ref(v_c_4004_);
lean_dec_ref(v_errorMsg_4003_);
return v_s_4005_;
}
else
{
lean_object* v_toInputContext_4008_; lean_object* v_val_4009_; lean_object* v_fileMap_4010_; lean_object* v_pos_4011_; lean_object* v_savedPos_4012_; lean_object* v_pos_4013_; lean_object* v_column_4014_; lean_object* v_column_4015_; uint8_t v___x_4016_; 
v_toInputContext_4008_ = lean_ctor_get(v_c_4004_, 0);
lean_inc_ref(v_toInputContext_4008_);
lean_dec_ref(v_c_4004_);
v_val_4009_ = lean_ctor_get(v_savedPos_x3f_4007_, 0);
lean_inc(v_val_4009_);
lean_dec_ref_known(v_savedPos_x3f_4007_, 1);
v_fileMap_4010_ = lean_ctor_get(v_toInputContext_4008_, 2);
lean_inc_ref_n(v_fileMap_4010_, 2);
lean_dec_ref(v_toInputContext_4008_);
v_pos_4011_ = lean_ctor_get(v_s_4005_, 2);
v_savedPos_4012_ = l_Lean_FileMap_toPosition(v_fileMap_4010_, v_val_4009_);
lean_dec(v_val_4009_);
v_pos_4013_ = l_Lean_FileMap_toPosition(v_fileMap_4010_, v_pos_4011_);
v_column_4014_ = lean_ctor_get(v_pos_4013_, 1);
lean_inc(v_column_4014_);
lean_dec_ref(v_pos_4013_);
v_column_4015_ = lean_ctor_get(v_savedPos_4012_, 1);
lean_inc(v_column_4015_);
lean_dec_ref(v_savedPos_4012_);
v___x_4016_ = lean_nat_dec_eq(v_column_4014_, v_column_4015_);
lean_dec(v_column_4015_);
lean_dec(v_column_4014_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_Parser_ParserState_mkError(v_s_4005_, v_errorMsg_4003_);
return v___x_4017_;
}
else
{
lean_dec_ref(v_errorMsg_4003_);
return v_s_4005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_4018_){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4020_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_4020_, 0, v_errorMsg_4018_);
v___x_4021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4019_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4029_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4030_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4031_ = l_Lean_addBuiltinDocString(v___x_4029_, v___x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4034_, lean_object* v_c_4035_, lean_object* v_s_4036_){
_start:
{
lean_object* v_toCacheableParserContext_4037_; lean_object* v_savedPos_x3f_4038_; 
v_toCacheableParserContext_4037_ = lean_ctor_get(v_c_4035_, 2);
v_savedPos_x3f_4038_ = lean_ctor_get(v_toCacheableParserContext_4037_, 2);
lean_inc(v_savedPos_x3f_4038_);
if (lean_obj_tag(v_savedPos_x3f_4038_) == 0)
{
lean_dec_ref(v_c_4035_);
lean_dec_ref(v_errorMsg_4034_);
return v_s_4036_;
}
else
{
lean_object* v_toInputContext_4039_; lean_object* v_val_4040_; lean_object* v_fileMap_4041_; lean_object* v_pos_4042_; lean_object* v_savedPos_4043_; lean_object* v_column_4044_; lean_object* v_pos_4045_; lean_object* v_column_4046_; uint8_t v___x_4047_; 
v_toInputContext_4039_ = lean_ctor_get(v_c_4035_, 0);
lean_inc_ref(v_toInputContext_4039_);
lean_dec_ref(v_c_4035_);
v_val_4040_ = lean_ctor_get(v_savedPos_x3f_4038_, 0);
lean_inc(v_val_4040_);
lean_dec_ref_known(v_savedPos_x3f_4038_, 1);
v_fileMap_4041_ = lean_ctor_get(v_toInputContext_4039_, 2);
lean_inc_ref_n(v_fileMap_4041_, 2);
lean_dec_ref(v_toInputContext_4039_);
v_pos_4042_ = lean_ctor_get(v_s_4036_, 2);
v_savedPos_4043_ = l_Lean_FileMap_toPosition(v_fileMap_4041_, v_val_4040_);
lean_dec(v_val_4040_);
v_column_4044_ = lean_ctor_get(v_savedPos_4043_, 1);
lean_inc(v_column_4044_);
lean_dec_ref(v_savedPos_4043_);
v_pos_4045_ = l_Lean_FileMap_toPosition(v_fileMap_4041_, v_pos_4042_);
v_column_4046_ = lean_ctor_get(v_pos_4045_, 1);
lean_inc(v_column_4046_);
lean_dec_ref(v_pos_4045_);
v___x_4047_ = lean_nat_dec_le(v_column_4044_, v_column_4046_);
lean_dec(v_column_4046_);
lean_dec(v_column_4044_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_Parser_ParserState_mkError(v_s_4036_, v_errorMsg_4034_);
return v___x_4048_;
}
else
{
lean_dec_ref(v_errorMsg_4034_);
return v_s_4036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4049_){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4051_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4051_, 0, v_errorMsg_4049_);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4061_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4062_ = l_Lean_addBuiltinDocString(v___x_4060_, v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4065_, lean_object* v_c_4066_, lean_object* v_s_4067_){
_start:
{
lean_object* v_toCacheableParserContext_4068_; lean_object* v_savedPos_x3f_4069_; 
v_toCacheableParserContext_4068_ = lean_ctor_get(v_c_4066_, 2);
v_savedPos_x3f_4069_ = lean_ctor_get(v_toCacheableParserContext_4068_, 2);
lean_inc(v_savedPos_x3f_4069_);
if (lean_obj_tag(v_savedPos_x3f_4069_) == 0)
{
lean_dec_ref(v_c_4066_);
lean_dec_ref(v_errorMsg_4065_);
return v_s_4067_;
}
else
{
lean_object* v_toInputContext_4070_; lean_object* v_val_4071_; lean_object* v_fileMap_4072_; lean_object* v_pos_4073_; lean_object* v_savedPos_4074_; lean_object* v_column_4075_; lean_object* v_pos_4076_; lean_object* v_column_4077_; uint8_t v___x_4078_; 
v_toInputContext_4070_ = lean_ctor_get(v_c_4066_, 0);
lean_inc_ref(v_toInputContext_4070_);
lean_dec_ref(v_c_4066_);
v_val_4071_ = lean_ctor_get(v_savedPos_x3f_4069_, 0);
lean_inc(v_val_4071_);
lean_dec_ref_known(v_savedPos_x3f_4069_, 1);
v_fileMap_4072_ = lean_ctor_get(v_toInputContext_4070_, 2);
lean_inc_ref_n(v_fileMap_4072_, 2);
lean_dec_ref(v_toInputContext_4070_);
v_pos_4073_ = lean_ctor_get(v_s_4067_, 2);
v_savedPos_4074_ = l_Lean_FileMap_toPosition(v_fileMap_4072_, v_val_4071_);
lean_dec(v_val_4071_);
v_column_4075_ = lean_ctor_get(v_savedPos_4074_, 1);
lean_inc(v_column_4075_);
lean_dec_ref(v_savedPos_4074_);
v_pos_4076_ = l_Lean_FileMap_toPosition(v_fileMap_4072_, v_pos_4073_);
v_column_4077_ = lean_ctor_get(v_pos_4076_, 1);
lean_inc(v_column_4077_);
lean_dec_ref(v_pos_4076_);
v___x_4078_ = lean_nat_dec_lt(v_column_4075_, v_column_4077_);
lean_dec(v_column_4077_);
lean_dec(v_column_4075_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lean_Parser_ParserState_mkError(v_s_4067_, v_errorMsg_4065_);
return v___x_4079_;
}
else
{
lean_dec_ref(v_errorMsg_4065_);
return v_s_4067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4080_){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4082_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4082_, 0, v_errorMsg_4080_);
v___x_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4092_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4093_ = l_Lean_addBuiltinDocString(v___x_4091_, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4096_, lean_object* v_c_4097_, lean_object* v_s_4098_){
_start:
{
lean_object* v_toCacheableParserContext_4099_; lean_object* v_savedPos_x3f_4100_; 
v_toCacheableParserContext_4099_ = lean_ctor_get(v_c_4097_, 2);
v_savedPos_x3f_4100_ = lean_ctor_get(v_toCacheableParserContext_4099_, 2);
lean_inc(v_savedPos_x3f_4100_);
if (lean_obj_tag(v_savedPos_x3f_4100_) == 0)
{
lean_dec_ref(v_c_4097_);
lean_dec_ref(v_errorMsg_4096_);
return v_s_4098_;
}
else
{
lean_object* v_toInputContext_4101_; lean_object* v_val_4102_; lean_object* v_fileMap_4103_; lean_object* v_pos_4104_; lean_object* v_savedPos_4105_; lean_object* v_pos_4106_; lean_object* v_line_4107_; lean_object* v_line_4108_; uint8_t v___x_4109_; 
v_toInputContext_4101_ = lean_ctor_get(v_c_4097_, 0);
lean_inc_ref(v_toInputContext_4101_);
lean_dec_ref(v_c_4097_);
v_val_4102_ = lean_ctor_get(v_savedPos_x3f_4100_, 0);
lean_inc(v_val_4102_);
lean_dec_ref_known(v_savedPos_x3f_4100_, 1);
v_fileMap_4103_ = lean_ctor_get(v_toInputContext_4101_, 2);
lean_inc_ref_n(v_fileMap_4103_, 2);
lean_dec_ref(v_toInputContext_4101_);
v_pos_4104_ = lean_ctor_get(v_s_4098_, 2);
v_savedPos_4105_ = l_Lean_FileMap_toPosition(v_fileMap_4103_, v_val_4102_);
lean_dec(v_val_4102_);
v_pos_4106_ = l_Lean_FileMap_toPosition(v_fileMap_4103_, v_pos_4104_);
v_line_4107_ = lean_ctor_get(v_pos_4106_, 0);
lean_inc(v_line_4107_);
lean_dec_ref(v_pos_4106_);
v_line_4108_ = lean_ctor_get(v_savedPos_4105_, 0);
lean_inc(v_line_4108_);
lean_dec_ref(v_savedPos_4105_);
v___x_4109_ = lean_nat_dec_eq(v_line_4107_, v_line_4108_);
lean_dec(v_line_4108_);
lean_dec(v_line_4107_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_Parser_ParserState_mkError(v_s_4098_, v_errorMsg_4096_);
return v___x_4110_;
}
else
{
lean_dec_ref(v_errorMsg_4096_);
return v_s_4098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4111_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4113_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4113_, 0, v_errorMsg_4111_);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4112_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4123_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4124_ = l_Lean_addBuiltinDocString(v___x_4122_, v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4127_, lean_object* v_x_4128_){
_start:
{
lean_object* v_prec_4129_; lean_object* v_quotDepth_4130_; uint8_t v_suppressInsideQuot_4131_; lean_object* v_forbiddenTks_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4141_; 
v_prec_4129_ = lean_ctor_get(v_x_4128_, 0);
v_quotDepth_4130_ = lean_ctor_get(v_x_4128_, 1);
v_suppressInsideQuot_4131_ = lean_ctor_get_uint8(v_x_4128_, sizeof(void*)*4);
v_forbiddenTks_4132_ = lean_ctor_get(v_x_4128_, 3);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_x_4128_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; 
v_unused_4142_ = lean_ctor_get(v_x_4128_, 2);
lean_dec(v_unused_4142_);
v___x_4134_ = v_x_4128_;
v_isShared_4135_ = v_isSharedCheck_4141_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_forbiddenTks_4132_);
lean_inc(v_quotDepth_4130_);
lean_inc(v_prec_4129_);
lean_dec(v_x_4128_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4141_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v_pos_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
v_pos_4136_ = lean_ctor_get(v___y_4127_, 2);
lean_inc(v_pos_4136_);
v___x_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4137_, 0, v_pos_4136_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 2, v___x_4137_);
v___x_4139_ = v___x_4134_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_prec_4129_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_quotDepth_4130_);
lean_ctor_set(v_reuseFailAlloc_4140_, 2, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4140_, 3, v_forbiddenTks_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4140_, sizeof(void*)*4, v_suppressInsideQuot_4131_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4143_, lean_object* v_x_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_Parser_withPosition___lam__0(v___y_4143_, v_x_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v___f_4149_; lean_object* v___x_4150_; 
lean_inc_ref(v___y_4148_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4149_, 0, v___y_4148_);
v___x_4150_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4149_, v_fn_4146_, v___y_4147_, v___y_4148_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4151_){
_start:
{
lean_object* v_info_4152_; lean_object* v_fn_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4161_; 
v_info_4152_ = lean_ctor_get(v_p_4151_, 0);
v_fn_4153_ = lean_ctor_get(v_p_4151_, 1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_p_4151_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4155_ = v_p_4151_;
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_fn_4153_);
lean_inc(v_info_4152_);
lean_dec(v_p_4151_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___f_4157_; lean_object* v___x_4159_; 
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4157_, 0, v_fn_4153_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 1, v___f_4157_);
v___x_4159_ = v___x_4155_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_info_4152_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___f_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4169_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4170_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4171_ = l_Lean_addBuiltinDocString(v___x_4169_, v___x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4174_, lean_object* v_pos_4175_, lean_object* v_c_4176_){
_start:
{
uint8_t v___x_4177_; 
v___x_4177_ = l_Lean_Parser_checkTailLinebreak(v_prev_4174_);
if (v___x_4177_ == 0)
{
lean_dec(v_pos_4175_);
return v_c_4176_;
}
else
{
lean_object* v_prec_4178_; lean_object* v_quotDepth_4179_; uint8_t v_suppressInsideQuot_4180_; lean_object* v_forbiddenTks_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4189_; 
v_prec_4178_ = lean_ctor_get(v_c_4176_, 0);
v_quotDepth_4179_ = lean_ctor_get(v_c_4176_, 1);
v_suppressInsideQuot_4180_ = lean_ctor_get_uint8(v_c_4176_, sizeof(void*)*4);
v_forbiddenTks_4181_ = lean_ctor_get(v_c_4176_, 3);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_c_4176_);
if (v_isSharedCheck_4189_ == 0)
{
lean_object* v_unused_4190_; 
v_unused_4190_ = lean_ctor_get(v_c_4176_, 2);
lean_dec(v_unused_4190_);
v___x_4183_ = v_c_4176_;
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_forbiddenTks_4181_);
lean_inc(v_quotDepth_4179_);
lean_inc(v_prec_4178_);
lean_dec(v_c_4176_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4185_, 0, v_pos_4175_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 2, v___x_4185_);
v___x_4187_ = v___x_4183_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_prec_4178_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_quotDepth_4179_);
lean_ctor_set(v_reuseFailAlloc_4188_, 2, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4188_, 3, v_forbiddenTks_4181_);
lean_ctor_set_uint8(v_reuseFailAlloc_4188_, sizeof(void*)*4, v_suppressInsideQuot_4180_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4191_, lean_object* v_pos_4192_, lean_object* v_c_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4191_, v_pos_4192_, v_c_4193_);
lean_dec(v_prev_4191_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_stxStack_4198_; lean_object* v_pos_4199_; lean_object* v_prev_4200_; lean_object* v___f_4201_; lean_object* v___x_4202_; 
v_stxStack_4198_ = lean_ctor_get(v___y_4197_, 0);
v_pos_4199_ = lean_ctor_get(v___y_4197_, 2);
v_prev_4200_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4198_);
lean_inc(v_pos_4199_);
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4201_, 0, v_prev_4200_);
lean_closure_set(v___f_4201_, 1, v_pos_4199_);
v___x_4202_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4201_, v_fn_4195_, v___y_4196_, v___y_4197_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4203_){
_start:
{
lean_object* v_info_4204_; lean_object* v_fn_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4213_; 
v_info_4204_ = lean_ctor_get(v_p_4203_, 0);
v_fn_4205_ = lean_ctor_get(v_p_4203_, 1);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_p_4203_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4207_ = v_p_4203_;
v_isShared_4208_ = v_isSharedCheck_4213_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_fn_4205_);
lean_inc(v_info_4204_);
lean_dec(v_p_4203_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4213_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___f_4209_; lean_object* v___x_4211_; 
v___f_4209_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4209_, 0, v_fn_4205_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 1, v___f_4209_);
v___x_4211_ = v___x_4207_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_info_4204_);
lean_ctor_set(v_reuseFailAlloc_4212_, 1, v___f_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4214_){
_start:
{
lean_object* v_prec_4215_; lean_object* v_quotDepth_4216_; uint8_t v_suppressInsideQuot_4217_; lean_object* v_forbiddenTks_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4226_; 
v_prec_4215_ = lean_ctor_get(v_x_4214_, 0);
v_quotDepth_4216_ = lean_ctor_get(v_x_4214_, 1);
v_suppressInsideQuot_4217_ = lean_ctor_get_uint8(v_x_4214_, sizeof(void*)*4);
v_forbiddenTks_4218_ = lean_ctor_get(v_x_4214_, 3);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_x_4214_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; 
v_unused_4227_ = lean_ctor_get(v_x_4214_, 2);
lean_dec(v_unused_4227_);
v___x_4220_ = v_x_4214_;
v_isShared_4221_ = v_isSharedCheck_4226_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_forbiddenTks_4218_);
lean_inc(v_quotDepth_4216_);
lean_inc(v_prec_4215_);
lean_dec(v_x_4214_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4226_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4222_ = lean_box(0);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 2, v___x_4222_);
v___x_4224_ = v___x_4220_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_prec_4215_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_quotDepth_4216_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v___x_4222_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_forbiddenTks_4218_);
lean_ctor_set_uint8(v_reuseFailAlloc_4225_, sizeof(void*)*4, v_suppressInsideQuot_4217_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4229_){
_start:
{
lean_object* v___f_4230_; lean_object* v___x_4231_; 
v___f_4230_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4231_ = l_Lean_Parser_adaptCacheableContext(v___f_4230_, v_p_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4239_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4240_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4241_ = l_Lean_addBuiltinDocString(v___x_4239_, v___x_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4244_, lean_object* v_c_4245_){
_start:
{
lean_object* v_prec_4246_; lean_object* v_quotDepth_4247_; uint8_t v_suppressInsideQuot_4248_; lean_object* v_savedPos_x3f_4249_; lean_object* v_forbiddenTks_4250_; uint8_t v___x_4251_; 
v_prec_4246_ = lean_ctor_get(v_c_4245_, 0);
v_quotDepth_4247_ = lean_ctor_get(v_c_4245_, 1);
v_suppressInsideQuot_4248_ = lean_ctor_get_uint8(v_c_4245_, sizeof(void*)*4);
v_savedPos_x3f_4249_ = lean_ctor_get(v_c_4245_, 2);
v_forbiddenTks_4250_ = lean_ctor_get(v_c_4245_, 3);
v___x_4251_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_4250_, v_tk_4244_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4259_; 
lean_inc_ref(v_forbiddenTks_4250_);
lean_inc(v_savedPos_x3f_4249_);
lean_inc(v_quotDepth_4247_);
lean_inc(v_prec_4246_);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_c_4245_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; lean_object* v_unused_4261_; lean_object* v_unused_4262_; lean_object* v_unused_4263_; 
v_unused_4260_ = lean_ctor_get(v_c_4245_, 3);
lean_dec(v_unused_4260_);
v_unused_4261_ = lean_ctor_get(v_c_4245_, 2);
lean_dec(v_unused_4261_);
v_unused_4262_ = lean_ctor_get(v_c_4245_, 1);
lean_dec(v_unused_4262_);
v_unused_4263_ = lean_ctor_get(v_c_4245_, 0);
lean_dec(v_unused_4263_);
v___x_4253_ = v_c_4245_;
v_isShared_4254_ = v_isSharedCheck_4259_;
goto v_resetjp_4252_;
}
else
{
lean_dec(v_c_4245_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4259_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4255_ = lean_array_push(v_forbiddenTks_4250_, v_tk_4244_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 3, v___x_4255_);
v___x_4257_ = v___x_4253_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_prec_4246_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_quotDepth_4247_);
lean_ctor_set(v_reuseFailAlloc_4258_, 2, v_savedPos_x3f_4249_);
lean_ctor_set(v_reuseFailAlloc_4258_, 3, v___x_4255_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*4, v_suppressInsideQuot_4248_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
else
{
lean_dec_ref(v_tk_4244_);
return v_c_4245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4264_, lean_object* v_p_4265_){
_start:
{
lean_object* v___f_4266_; lean_object* v___x_4267_; 
v___f_4266_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4266_, 0, v_tk_4264_);
v___x_4267_ = l_Lean_Parser_adaptCacheableContext(v___f_4266_, v_p_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4276_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4277_ = l_Lean_addBuiltinDocString(v___x_4275_, v___x_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4279_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(lean_object* v_a_4280_, lean_object* v_as_4281_, size_t v_i_4282_, size_t v_stop_4283_){
_start:
{
uint8_t v___x_4284_; 
v___x_4284_ = lean_usize_dec_eq(v_i_4282_, v_stop_4283_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4285_ = lean_array_uget_borrowed(v_as_4281_, v_i_4282_);
v___x_4286_ = lean_string_dec_eq(v___x_4285_, v_a_4280_);
if (v___x_4286_ == 0)
{
size_t v___x_4287_; size_t v___x_4288_; 
v___x_4287_ = ((size_t)1ULL);
v___x_4288_ = lean_usize_add(v_i_4282_, v___x_4287_);
v_i_4282_ = v___x_4288_;
goto _start;
}
else
{
return v___x_4286_;
}
}
else
{
uint8_t v___x_4290_; 
v___x_4290_ = 0;
return v___x_4290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0___boxed(lean_object* v_a_4291_, lean_object* v_as_4292_, lean_object* v_i_4293_, lean_object* v_stop_4294_){
_start:
{
size_t v_i_boxed_4295_; size_t v_stop_boxed_4296_; uint8_t v_res_4297_; lean_object* v_r_4298_; 
v_i_boxed_4295_ = lean_unbox_usize(v_i_4293_);
lean_dec(v_i_4293_);
v_stop_boxed_4296_ = lean_unbox_usize(v_stop_4294_);
lean_dec(v_stop_4294_);
v_res_4297_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4291_, v_as_4292_, v_i_boxed_4295_, v_stop_boxed_4296_);
lean_dec_ref(v_as_4292_);
lean_dec_ref(v_a_4291_);
v_r_4298_ = lean_box(v_res_4297_);
return v_r_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(lean_object* v_size_4299_, lean_object* v_as_4300_, size_t v_sz_4301_, size_t v_i_4302_, lean_object* v_b_4303_){
_start:
{
lean_object* v_a_4305_; uint8_t v___x_4309_; 
v___x_4309_ = lean_usize_dec_lt(v_i_4302_, v_sz_4301_);
if (v___x_4309_ == 0)
{
lean_dec(v_size_4299_);
return v_b_4303_;
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4313_; lean_object* v___y_4315_; uint8_t v___x_4320_; 
v_a_4310_ = lean_array_uget_borrowed(v_as_4300_, v_i_4302_);
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4320_ = lean_nat_dec_lt(v___x_4313_, v_size_4299_);
if (v___x_4320_ == 0)
{
goto v___jp_4311_;
}
else
{
lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4321_ = lean_array_get_size(v_b_4303_);
v___x_4322_ = lean_nat_dec_le(v_size_4299_, v___x_4321_);
if (v___x_4322_ == 0)
{
v___y_4315_ = v___x_4321_;
goto v___jp_4314_;
}
else
{
lean_inc(v_size_4299_);
v___y_4315_ = v_size_4299_;
goto v___jp_4314_;
}
}
v___jp_4311_:
{
lean_object* v___x_4312_; 
lean_inc(v_a_4310_);
v___x_4312_ = lean_array_push(v_b_4303_, v_a_4310_);
v_a_4305_ = v___x_4312_;
goto v___jp_4304_;
}
v___jp_4314_:
{
uint8_t v___x_4316_; 
v___x_4316_ = lean_nat_dec_lt(v___x_4313_, v___y_4315_);
if (v___x_4316_ == 0)
{
lean_dec(v___y_4315_);
goto v___jp_4311_;
}
else
{
size_t v___x_4317_; size_t v___x_4318_; uint8_t v___x_4319_; 
v___x_4317_ = ((size_t)0ULL);
v___x_4318_ = lean_usize_of_nat(v___y_4315_);
lean_dec(v___y_4315_);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4310_, v_b_4303_, v___x_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
goto v___jp_4311_;
}
else
{
v_a_4305_ = v_b_4303_;
goto v___jp_4304_;
}
}
}
}
v___jp_4304_:
{
size_t v___x_4306_; size_t v___x_4307_; 
v___x_4306_ = ((size_t)1ULL);
v___x_4307_ = lean_usize_add(v_i_4302_, v___x_4306_);
v_i_4302_ = v___x_4307_;
v_b_4303_ = v_a_4305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1___boxed(lean_object* v_size_4323_, lean_object* v_as_4324_, lean_object* v_sz_4325_, lean_object* v_i_4326_, lean_object* v_b_4327_){
_start:
{
size_t v_sz_boxed_4328_; size_t v_i_boxed_4329_; lean_object* v_res_4330_; 
v_sz_boxed_4328_ = lean_unbox_usize(v_sz_4325_);
lean_dec(v_sz_4325_);
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4323_, v_as_4324_, v_sz_boxed_4328_, v_i_boxed_4329_, v_b_4327_);
lean_dec_ref(v_as_4324_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(lean_object* v_init_4331_, lean_object* v_tks_4332_){
_start:
{
lean_object* v_size_4333_; size_t v_sz_4334_; size_t v___x_4335_; lean_object* v___x_4336_; 
v_size_4333_ = lean_array_get_size(v_init_4331_);
v_sz_4334_ = lean_array_size(v_tks_4332_);
v___x_4335_ = ((size_t)0ULL);
v___x_4336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4333_, v_tks_4332_, v_sz_4334_, v___x_4335_, v_init_4331_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks___boxed(lean_object* v_init_4337_, lean_object* v_tks_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_init_4337_, v_tks_4338_);
lean_dec_ref(v_tks_4338_);
return v_res_4339_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__6));
v___x_4362_ = l_Lean_mkAtom(v___x_4361_);
return v___x_4362_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__8, &l_Lean_Parser_withForbiddens___auto__1___closed__8_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__8);
v___x_4364_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4365_ = lean_array_push(v___x_4364_, v___x_4363_);
return v___x_4365_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_4377_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4378_ = lean_array_push(v___x_4377_, v___x_4376_);
return v___x_4378_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4379_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__13, &l_Lean_Parser_withForbiddens___auto__1___closed__13_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__13);
v___x_4380_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__11));
v___x_4381_ = lean_box(2);
v___x_4382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
lean_ctor_set(v___x_4382_, 1, v___x_4380_);
lean_ctor_set(v___x_4382_, 2, v___x_4379_);
return v___x_4382_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4383_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__14, &l_Lean_Parser_withForbiddens___auto__1___closed__14_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__14);
v___x_4384_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__9, &l_Lean_Parser_withForbiddens___auto__1___closed__9_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__9);
v___x_4385_ = lean_array_push(v___x_4384_, v___x_4383_);
return v___x_4385_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4386_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__15, &l_Lean_Parser_withForbiddens___auto__1___closed__15_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__15);
v___x_4387_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__7));
v___x_4388_ = lean_box(2);
v___x_4389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
lean_ctor_set(v___x_4389_, 1, v___x_4387_);
lean_ctor_set(v___x_4389_, 2, v___x_4386_);
return v___x_4389_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__16, &l_Lean_Parser_withForbiddens___auto__1___closed__16_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__16);
v___x_4391_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4392_ = lean_array_push(v___x_4391_, v___x_4390_);
return v___x_4392_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4393_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__17, &l_Lean_Parser_withForbiddens___auto__1___closed__17_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__17);
v___x_4394_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_4395_ = lean_box(2);
v___x_4396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
lean_ctor_set(v___x_4396_, 1, v___x_4394_);
lean_ctor_set(v___x_4396_, 2, v___x_4393_);
return v___x_4396_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4397_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__18, &l_Lean_Parser_withForbiddens___auto__1___closed__18_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__18);
v___x_4398_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4399_ = lean_array_push(v___x_4398_, v___x_4397_);
return v___x_4399_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4400_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__19, &l_Lean_Parser_withForbiddens___auto__1___closed__19_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__19);
v___x_4401_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__5));
v___x_4402_ = lean_box(2);
v___x_4403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4402_);
lean_ctor_set(v___x_4403_, 1, v___x_4401_);
lean_ctor_set(v___x_4403_, 2, v___x_4400_);
return v___x_4403_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__20, &l_Lean_Parser_withForbiddens___auto__1___closed__20_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__20);
v___x_4405_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4406_ = lean_array_push(v___x_4405_, v___x_4404_);
return v___x_4406_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4407_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__21, &l_Lean_Parser_withForbiddens___auto__1___closed__21_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__21);
v___x_4408_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__2));
v___x_4409_ = lean_box(2);
v___x_4410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
lean_ctor_set(v___x_4410_, 1, v___x_4408_);
lean_ctor_set(v___x_4410_, 2, v___x_4407_);
return v___x_4410_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1(void){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__22, &l_Lean_Parser_withForbiddens___auto__1___closed__22_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__22);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg___lam__0(lean_object* v_tks_4412_, lean_object* v_c_4413_){
_start:
{
lean_object* v_prec_4414_; lean_object* v_quotDepth_4415_; uint8_t v_suppressInsideQuot_4416_; lean_object* v_savedPos_x3f_4417_; lean_object* v_forbiddenTks_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4432_; 
v_prec_4414_ = lean_ctor_get(v_c_4413_, 0);
v_quotDepth_4415_ = lean_ctor_get(v_c_4413_, 1);
v_suppressInsideQuot_4416_ = lean_ctor_get_uint8(v_c_4413_, sizeof(void*)*4);
v_savedPos_x3f_4417_ = lean_ctor_get(v_c_4413_, 2);
v_forbiddenTks_4418_ = lean_ctor_get(v_c_4413_, 3);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_c_4413_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4420_ = v_c_4413_;
v_isShared_4421_ = v_isSharedCheck_4432_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_forbiddenTks_4418_);
lean_inc(v_savedPos_x3f_4417_);
lean_inc(v_quotDepth_4415_);
lean_inc(v_prec_4414_);
lean_dec(v_c_4413_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4432_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
v___x_4422_ = lean_array_get_size(v_forbiddenTks_4418_);
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = lean_nat_dec_eq(v___x_4422_, v___x_4423_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4425_; lean_object* v___x_4427_; 
v___x_4425_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_forbiddenTks_4418_, v_tks_4412_);
lean_dec_ref(v_tks_4412_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 3, v___x_4425_);
v___x_4427_ = v___x_4420_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_prec_4414_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_quotDepth_4415_);
lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_savedPos_x3f_4417_);
lean_ctor_set(v_reuseFailAlloc_4428_, 3, v___x_4425_);
lean_ctor_set_uint8(v_reuseFailAlloc_4428_, sizeof(void*)*4, v_suppressInsideQuot_4416_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
else
{
lean_object* v___x_4430_; 
lean_dec_ref(v_forbiddenTks_4418_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 3, v_tks_4412_);
v___x_4430_ = v___x_4420_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_prec_4414_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v_quotDepth_4415_);
lean_ctor_set(v_reuseFailAlloc_4431_, 2, v_savedPos_x3f_4417_);
lean_ctor_set(v_reuseFailAlloc_4431_, 3, v_tks_4412_);
lean_ctor_set_uint8(v_reuseFailAlloc_4431_, sizeof(void*)*4, v_suppressInsideQuot_4416_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg(lean_object* v_tks_4433_, lean_object* v_p_4434_){
_start:
{
lean_object* v___f_4435_; lean_object* v___x_4436_; 
v___f_4435_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbiddens___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4435_, 0, v_tks_4433_);
v___x_4436_ = l_Lean_Parser_adaptCacheableContext(v___f_4435_, v_p_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens(lean_object* v_tks_4437_, lean_object* v_p_4438_, lean_object* v___h_4439_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_Lean_Parser_withForbiddens___redArg(v_tks_4437_, v_p_4438_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1(){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4448_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1));
v___x_4449_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2));
v___x_4450_ = l_Lean_addBuiltinDocString(v___x_4448_, v___x_4449_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___boxed(lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4455_){
_start:
{
lean_object* v_prec_4456_; lean_object* v_quotDepth_4457_; uint8_t v_suppressInsideQuot_4458_; lean_object* v_savedPos_x3f_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4467_; 
v_prec_4456_ = lean_ctor_get(v_x_4455_, 0);
v_quotDepth_4457_ = lean_ctor_get(v_x_4455_, 1);
v_suppressInsideQuot_4458_ = lean_ctor_get_uint8(v_x_4455_, sizeof(void*)*4);
v_savedPos_x3f_4459_ = lean_ctor_get(v_x_4455_, 2);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_x_4455_);
if (v_isSharedCheck_4467_ == 0)
{
lean_object* v_unused_4468_; 
v_unused_4468_ = lean_ctor_get(v_x_4455_, 3);
lean_dec(v_unused_4468_);
v___x_4461_ = v_x_4455_;
v_isShared_4462_ = v_isSharedCheck_4467_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_savedPos_x3f_4459_);
lean_inc(v_quotDepth_4457_);
lean_inc(v_prec_4456_);
lean_dec(v_x_4455_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4467_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4463_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___lam__0___closed__0));
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 3, v___x_4463_);
v___x_4465_ = v___x_4461_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_prec_4456_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v_quotDepth_4457_);
lean_ctor_set(v_reuseFailAlloc_4466_, 2, v_savedPos_x3f_4459_);
lean_ctor_set(v_reuseFailAlloc_4466_, 3, v___x_4463_);
lean_ctor_set_uint8(v_reuseFailAlloc_4466_, sizeof(void*)*4, v_suppressInsideQuot_4458_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4470_){
_start:
{
lean_object* v___f_4471_; lean_object* v___x_4472_; 
v___f_4471_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4472_ = l_Lean_Parser_adaptCacheableContext(v___f_4471_, v_p_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4480_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4481_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4482_ = l_Lean_addBuiltinDocString(v___x_4480_, v___x_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4486_, lean_object* v_s_4487_){
_start:
{
lean_object* v_pos_4488_; lean_object* v_toInputContext_4489_; uint8_t v___x_4490_; 
v_pos_4488_ = lean_ctor_get(v_s_4487_, 2);
v_toInputContext_4489_ = lean_ctor_get(v_c_4486_, 0);
v___x_4490_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4489_, v_pos_4488_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4492_ = l_Lean_Parser_ParserState_mkError(v_s_4487_, v___x_4491_);
return v___x_4492_;
}
else
{
return v_s_4487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4493_, lean_object* v_s_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Lean_Parser_eoiFn(v_c_4493_, v_s_4494_);
lean_dec_ref(v_c_4493_);
return v_res_4495_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4497_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
lean_ctor_set(v___x_4498_, 1, v___x_4496_);
return v___x_4498_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4499_; 
v___x_4499_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4500_, lean_object* v_v_4501_, lean_object* v_t_4502_){
_start:
{
if (lean_obj_tag(v_t_4502_) == 0)
{
lean_object* v_size_4503_; lean_object* v_k_4504_; lean_object* v_v_4505_; lean_object* v_l_4506_; lean_object* v_r_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4787_; 
v_size_4503_ = lean_ctor_get(v_t_4502_, 0);
v_k_4504_ = lean_ctor_get(v_t_4502_, 1);
v_v_4505_ = lean_ctor_get(v_t_4502_, 2);
v_l_4506_ = lean_ctor_get(v_t_4502_, 3);
v_r_4507_ = lean_ctor_get(v_t_4502_, 4);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_t_4502_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4509_ = v_t_4502_;
v_isShared_4510_ = v_isSharedCheck_4787_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_r_4507_);
lean_inc(v_l_4506_);
lean_inc(v_v_4505_);
lean_inc(v_k_4504_);
lean_inc(v_size_4503_);
lean_dec(v_t_4502_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4787_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
uint8_t v___x_4511_; 
v___x_4511_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4500_, v_k_4504_);
switch(v___x_4511_)
{
case 0:
{
lean_object* v_impl_4512_; lean_object* v___x_4513_; 
lean_dec(v_size_4503_);
v_impl_4512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4500_, v_v_4501_, v_l_4506_);
v___x_4513_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4507_) == 0)
{
lean_object* v_size_4514_; lean_object* v_size_4515_; lean_object* v_k_4516_; lean_object* v_v_4517_; lean_object* v_l_4518_; lean_object* v_r_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v_size_4514_ = lean_ctor_get(v_r_4507_, 0);
v_size_4515_ = lean_ctor_get(v_impl_4512_, 0);
lean_inc(v_size_4515_);
v_k_4516_ = lean_ctor_get(v_impl_4512_, 1);
lean_inc(v_k_4516_);
v_v_4517_ = lean_ctor_get(v_impl_4512_, 2);
lean_inc(v_v_4517_);
v_l_4518_ = lean_ctor_get(v_impl_4512_, 3);
lean_inc(v_l_4518_);
v_r_4519_ = lean_ctor_get(v_impl_4512_, 4);
lean_inc(v_r_4519_);
v___x_4520_ = lean_unsigned_to_nat(3u);
v___x_4521_ = lean_nat_mul(v___x_4520_, v_size_4514_);
v___x_4522_ = lean_nat_dec_lt(v___x_4521_, v_size_4515_);
lean_dec(v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
lean_dec(v_r_4519_);
lean_dec(v_l_4518_);
lean_dec(v_v_4517_);
lean_dec(v_k_4516_);
v___x_4523_ = lean_nat_add(v___x_4513_, v_size_4515_);
lean_dec(v_size_4515_);
v___x_4524_ = lean_nat_add(v___x_4523_, v_size_4514_);
lean_dec(v___x_4523_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 3, v_impl_4512_);
lean_ctor_set(v___x_4509_, 0, v___x_4524_);
v___x_4526_ = v___x_4509_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4527_, 3, v_impl_4512_);
lean_ctor_set(v_reuseFailAlloc_4527_, 4, v_r_4507_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
else
{
lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4593_; 
v_isSharedCheck_4593_ = !lean_is_exclusive(v_impl_4512_);
if (v_isSharedCheck_4593_ == 0)
{
lean_object* v_unused_4594_; lean_object* v_unused_4595_; lean_object* v_unused_4596_; lean_object* v_unused_4597_; lean_object* v_unused_4598_; 
v_unused_4594_ = lean_ctor_get(v_impl_4512_, 4);
lean_dec(v_unused_4594_);
v_unused_4595_ = lean_ctor_get(v_impl_4512_, 3);
lean_dec(v_unused_4595_);
v_unused_4596_ = lean_ctor_get(v_impl_4512_, 2);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_impl_4512_, 1);
lean_dec(v_unused_4597_);
v_unused_4598_ = lean_ctor_get(v_impl_4512_, 0);
lean_dec(v_unused_4598_);
v___x_4529_ = v_impl_4512_;
v_isShared_4530_ = v_isSharedCheck_4593_;
goto v_resetjp_4528_;
}
else
{
lean_dec(v_impl_4512_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4593_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v_size_4531_; lean_object* v_size_4532_; lean_object* v_k_4533_; lean_object* v_v_4534_; lean_object* v_l_4535_; lean_object* v_r_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v_size_4531_ = lean_ctor_get(v_l_4518_, 0);
v_size_4532_ = lean_ctor_get(v_r_4519_, 0);
v_k_4533_ = lean_ctor_get(v_r_4519_, 1);
v_v_4534_ = lean_ctor_get(v_r_4519_, 2);
v_l_4535_ = lean_ctor_get(v_r_4519_, 3);
v_r_4536_ = lean_ctor_get(v_r_4519_, 4);
v___x_4537_ = lean_unsigned_to_nat(2u);
v___x_4538_ = lean_nat_mul(v___x_4537_, v_size_4531_);
v___x_4539_ = lean_nat_dec_lt(v_size_4532_, v___x_4538_);
lean_dec(v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4568_; 
lean_inc(v_r_4536_);
lean_inc(v_l_4535_);
lean_inc(v_v_4534_);
lean_inc(v_k_4533_);
v_isSharedCheck_4568_ = !lean_is_exclusive(v_r_4519_);
if (v_isSharedCheck_4568_ == 0)
{
lean_object* v_unused_4569_; lean_object* v_unused_4570_; lean_object* v_unused_4571_; lean_object* v_unused_4572_; lean_object* v_unused_4573_; 
v_unused_4569_ = lean_ctor_get(v_r_4519_, 4);
lean_dec(v_unused_4569_);
v_unused_4570_ = lean_ctor_get(v_r_4519_, 3);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v_r_4519_, 2);
lean_dec(v_unused_4571_);
v_unused_4572_ = lean_ctor_get(v_r_4519_, 1);
lean_dec(v_unused_4572_);
v_unused_4573_ = lean_ctor_get(v_r_4519_, 0);
lean_dec(v_unused_4573_);
v___x_4541_ = v_r_4519_;
v_isShared_4542_ = v_isSharedCheck_4568_;
goto v_resetjp_4540_;
}
else
{
lean_dec(v_r_4519_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4568_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___x_4556_; lean_object* v___y_4558_; 
v___x_4543_ = lean_nat_add(v___x_4513_, v_size_4515_);
lean_dec(v_size_4515_);
v___x_4544_ = lean_nat_add(v___x_4543_, v_size_4514_);
lean_dec(v___x_4543_);
v___x_4556_ = lean_nat_add(v___x_4513_, v_size_4531_);
if (lean_obj_tag(v_l_4535_) == 0)
{
lean_object* v_size_4566_; 
v_size_4566_ = lean_ctor_get(v_l_4535_, 0);
lean_inc(v_size_4566_);
v___y_4558_ = v_size_4566_;
goto v___jp_4557_;
}
else
{
lean_object* v___x_4567_; 
v___x_4567_ = lean_unsigned_to_nat(0u);
v___y_4558_ = v___x_4567_;
goto v___jp_4557_;
}
v___jp_4545_:
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4549_ = lean_nat_add(v___y_4546_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec(v___y_4546_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 4, v_r_4507_);
lean_ctor_set(v___x_4541_, 3, v_r_4536_);
lean_ctor_set(v___x_4541_, 2, v_v_4505_);
lean_ctor_set(v___x_4541_, 1, v_k_4504_);
lean_ctor_set(v___x_4541_, 0, v___x_4549_);
v___x_4551_ = v___x_4541_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4555_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4555_, 3, v_r_4536_);
lean_ctor_set(v_reuseFailAlloc_4555_, 4, v_r_4507_);
v___x_4551_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4553_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 4, v___x_4551_);
lean_ctor_set(v___x_4529_, 3, v___y_4547_);
lean_ctor_set(v___x_4529_, 2, v_v_4534_);
lean_ctor_set(v___x_4529_, 1, v_k_4533_);
lean_ctor_set(v___x_4529_, 0, v___x_4544_);
v___x_4553_ = v___x_4529_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4544_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_k_4533_);
lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_v_4534_);
lean_ctor_set(v_reuseFailAlloc_4554_, 3, v___y_4547_);
lean_ctor_set(v_reuseFailAlloc_4554_, 4, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
v___jp_4557_:
{
lean_object* v___x_4559_; lean_object* v___x_4561_; 
v___x_4559_ = lean_nat_add(v___x_4556_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec(v___x_4556_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v_l_4535_);
lean_ctor_set(v___x_4509_, 3, v_l_4518_);
lean_ctor_set(v___x_4509_, 2, v_v_4517_);
lean_ctor_set(v___x_4509_, 1, v_k_4516_);
lean_ctor_set(v___x_4509_, 0, v___x_4559_);
v___x_4561_ = v___x_4509_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_k_4516_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_v_4517_);
lean_ctor_set(v_reuseFailAlloc_4565_, 3, v_l_4518_);
lean_ctor_set(v_reuseFailAlloc_4565_, 4, v_l_4535_);
v___x_4561_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_nat_add(v___x_4513_, v_size_4514_);
if (lean_obj_tag(v_r_4536_) == 0)
{
lean_object* v_size_4563_; 
v_size_4563_ = lean_ctor_get(v_r_4536_, 0);
lean_inc(v_size_4563_);
v___y_4546_ = v___x_4562_;
v___y_4547_ = v___x_4561_;
v___y_4548_ = v_size_4563_;
goto v___jp_4545_;
}
else
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_unsigned_to_nat(0u);
v___y_4546_ = v___x_4562_;
v___y_4547_ = v___x_4561_;
v___y_4548_ = v___x_4564_;
goto v___jp_4545_;
}
}
}
}
}
else
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4579_; 
lean_del_object(v___x_4509_);
v___x_4574_ = lean_nat_add(v___x_4513_, v_size_4515_);
lean_dec(v_size_4515_);
v___x_4575_ = lean_nat_add(v___x_4574_, v_size_4514_);
lean_dec(v___x_4574_);
v___x_4576_ = lean_nat_add(v___x_4513_, v_size_4514_);
v___x_4577_ = lean_nat_add(v___x_4576_, v_size_4532_);
lean_dec(v___x_4576_);
lean_inc_ref(v_r_4507_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 4, v_r_4507_);
lean_ctor_set(v___x_4529_, 3, v_r_4519_);
lean_ctor_set(v___x_4529_, 2, v_v_4505_);
lean_ctor_set(v___x_4529_, 1, v_k_4504_);
lean_ctor_set(v___x_4529_, 0, v___x_4577_);
v___x_4579_ = v___x_4529_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4592_, 3, v_r_4519_);
lean_ctor_set(v_reuseFailAlloc_4592_, 4, v_r_4507_);
v___x_4579_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
v_isSharedCheck_4586_ = !lean_is_exclusive(v_r_4507_);
if (v_isSharedCheck_4586_ == 0)
{
lean_object* v_unused_4587_; lean_object* v_unused_4588_; lean_object* v_unused_4589_; lean_object* v_unused_4590_; lean_object* v_unused_4591_; 
v_unused_4587_ = lean_ctor_get(v_r_4507_, 4);
lean_dec(v_unused_4587_);
v_unused_4588_ = lean_ctor_get(v_r_4507_, 3);
lean_dec(v_unused_4588_);
v_unused_4589_ = lean_ctor_get(v_r_4507_, 2);
lean_dec(v_unused_4589_);
v_unused_4590_ = lean_ctor_get(v_r_4507_, 1);
lean_dec(v_unused_4590_);
v_unused_4591_ = lean_ctor_get(v_r_4507_, 0);
lean_dec(v_unused_4591_);
v___x_4581_ = v_r_4507_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_dec(v_r_4507_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 4, v___x_4579_);
lean_ctor_set(v___x_4581_, 3, v_l_4518_);
lean_ctor_set(v___x_4581_, 2, v_v_4517_);
lean_ctor_set(v___x_4581_, 1, v_k_4516_);
lean_ctor_set(v___x_4581_, 0, v___x_4575_);
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_k_4516_);
lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_v_4517_);
lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_l_4518_);
lean_ctor_set(v_reuseFailAlloc_4585_, 4, v___x_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4599_; 
v_l_4599_ = lean_ctor_get(v_impl_4512_, 3);
lean_inc(v_l_4599_);
if (lean_obj_tag(v_l_4599_) == 0)
{
lean_object* v_r_4600_; lean_object* v_k_4601_; lean_object* v_v_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4613_; 
v_r_4600_ = lean_ctor_get(v_impl_4512_, 4);
v_k_4601_ = lean_ctor_get(v_impl_4512_, 1);
v_v_4602_ = lean_ctor_get(v_impl_4512_, 2);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_impl_4512_);
if (v_isSharedCheck_4613_ == 0)
{
lean_object* v_unused_4614_; lean_object* v_unused_4615_; 
v_unused_4614_ = lean_ctor_get(v_impl_4512_, 3);
lean_dec(v_unused_4614_);
v_unused_4615_ = lean_ctor_get(v_impl_4512_, 0);
lean_dec(v_unused_4615_);
v___x_4604_ = v_impl_4512_;
v_isShared_4605_ = v_isSharedCheck_4613_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_r_4600_);
lean_inc(v_v_4602_);
lean_inc(v_k_4601_);
lean_dec(v_impl_4512_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4613_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4606_; lean_object* v___x_4608_; 
v___x_4606_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4600_);
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 3, v_r_4600_);
lean_ctor_set(v___x_4604_, 2, v_v_4505_);
lean_ctor_set(v___x_4604_, 1, v_k_4504_);
lean_ctor_set(v___x_4604_, 0, v___x_4513_);
v___x_4608_ = v___x_4604_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4612_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4612_, 3, v_r_4600_);
lean_ctor_set(v_reuseFailAlloc_4612_, 4, v_r_4600_);
v___x_4608_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4610_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v___x_4608_);
lean_ctor_set(v___x_4509_, 3, v_l_4599_);
lean_ctor_set(v___x_4509_, 2, v_v_4602_);
lean_ctor_set(v___x_4509_, 1, v_k_4601_);
lean_ctor_set(v___x_4509_, 0, v___x_4606_);
v___x_4610_ = v___x_4509_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_k_4601_);
lean_ctor_set(v_reuseFailAlloc_4611_, 2, v_v_4602_);
lean_ctor_set(v_reuseFailAlloc_4611_, 3, v_l_4599_);
lean_ctor_set(v_reuseFailAlloc_4611_, 4, v___x_4608_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
else
{
lean_object* v_r_4616_; 
v_r_4616_ = lean_ctor_get(v_impl_4512_, 4);
lean_inc(v_r_4616_);
if (lean_obj_tag(v_r_4616_) == 0)
{
lean_object* v_k_4617_; lean_object* v_v_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4641_; 
v_k_4617_ = lean_ctor_get(v_impl_4512_, 1);
v_v_4618_ = lean_ctor_get(v_impl_4512_, 2);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_impl_4512_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; lean_object* v_unused_4643_; lean_object* v_unused_4644_; 
v_unused_4642_ = lean_ctor_get(v_impl_4512_, 4);
lean_dec(v_unused_4642_);
v_unused_4643_ = lean_ctor_get(v_impl_4512_, 3);
lean_dec(v_unused_4643_);
v_unused_4644_ = lean_ctor_get(v_impl_4512_, 0);
lean_dec(v_unused_4644_);
v___x_4620_ = v_impl_4512_;
v_isShared_4621_ = v_isSharedCheck_4641_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_v_4618_);
lean_inc(v_k_4617_);
lean_dec(v_impl_4512_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4641_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v_k_4622_; lean_object* v_v_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4637_; 
v_k_4622_ = lean_ctor_get(v_r_4616_, 1);
v_v_4623_ = lean_ctor_get(v_r_4616_, 2);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_r_4616_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; lean_object* v_unused_4639_; lean_object* v_unused_4640_; 
v_unused_4638_ = lean_ctor_get(v_r_4616_, 4);
lean_dec(v_unused_4638_);
v_unused_4639_ = lean_ctor_get(v_r_4616_, 3);
lean_dec(v_unused_4639_);
v_unused_4640_ = lean_ctor_get(v_r_4616_, 0);
lean_dec(v_unused_4640_);
v___x_4625_ = v_r_4616_;
v_isShared_4626_ = v_isSharedCheck_4637_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_v_4623_);
lean_inc(v_k_4622_);
lean_dec(v_r_4616_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4637_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4629_; 
v___x_4627_ = lean_unsigned_to_nat(3u);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 4, v_l_4599_);
lean_ctor_set(v___x_4625_, 3, v_l_4599_);
lean_ctor_set(v___x_4625_, 2, v_v_4618_);
lean_ctor_set(v___x_4625_, 1, v_k_4617_);
lean_ctor_set(v___x_4625_, 0, v___x_4513_);
v___x_4629_ = v___x_4625_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_k_4617_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_v_4618_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_l_4599_);
lean_ctor_set(v_reuseFailAlloc_4636_, 4, v_l_4599_);
v___x_4629_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
lean_object* v___x_4631_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_l_4599_);
lean_ctor_set(v___x_4620_, 2, v_v_4505_);
lean_ctor_set(v___x_4620_, 1, v_k_4504_);
lean_ctor_set(v___x_4620_, 0, v___x_4513_);
v___x_4631_ = v___x_4620_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_l_4599_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v_l_4599_);
v___x_4631_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4633_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v___x_4631_);
lean_ctor_set(v___x_4509_, 3, v___x_4629_);
lean_ctor_set(v___x_4509_, 2, v_v_4623_);
lean_ctor_set(v___x_4509_, 1, v_k_4622_);
lean_ctor_set(v___x_4509_, 0, v___x_4627_);
v___x_4633_ = v___x_4509_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4627_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_k_4622_);
lean_ctor_set(v_reuseFailAlloc_4634_, 2, v_v_4623_);
lean_ctor_set(v_reuseFailAlloc_4634_, 3, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4634_, 4, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
}
else
{
lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4645_ = lean_unsigned_to_nat(2u);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v_r_4616_);
lean_ctor_set(v___x_4509_, 3, v_impl_4512_);
lean_ctor_set(v___x_4509_, 0, v___x_4645_);
v___x_4647_ = v___x_4509_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4648_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4648_, 3, v_impl_4512_);
lean_ctor_set(v_reuseFailAlloc_4648_, 4, v_r_4616_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4650_; 
lean_dec(v_v_4505_);
lean_dec(v_k_4504_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 2, v_v_4501_);
lean_ctor_set(v___x_4509_, 1, v_k_4500_);
v___x_4650_ = v___x_4509_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_size_4503_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v_k_4500_);
lean_ctor_set(v_reuseFailAlloc_4651_, 2, v_v_4501_);
lean_ctor_set(v_reuseFailAlloc_4651_, 3, v_l_4506_);
lean_ctor_set(v_reuseFailAlloc_4651_, 4, v_r_4507_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
default: 
{
lean_object* v_impl_4652_; lean_object* v___x_4653_; 
lean_dec(v_size_4503_);
v_impl_4652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4500_, v_v_4501_, v_r_4507_);
v___x_4653_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4506_) == 0)
{
lean_object* v_size_4654_; lean_object* v_size_4655_; lean_object* v_k_4656_; lean_object* v_v_4657_; lean_object* v_l_4658_; lean_object* v_r_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v_size_4654_ = lean_ctor_get(v_l_4506_, 0);
v_size_4655_ = lean_ctor_get(v_impl_4652_, 0);
lean_inc(v_size_4655_);
v_k_4656_ = lean_ctor_get(v_impl_4652_, 1);
lean_inc(v_k_4656_);
v_v_4657_ = lean_ctor_get(v_impl_4652_, 2);
lean_inc(v_v_4657_);
v_l_4658_ = lean_ctor_get(v_impl_4652_, 3);
lean_inc(v_l_4658_);
v_r_4659_ = lean_ctor_get(v_impl_4652_, 4);
lean_inc(v_r_4659_);
v___x_4660_ = lean_unsigned_to_nat(3u);
v___x_4661_ = lean_nat_mul(v___x_4660_, v_size_4654_);
v___x_4662_ = lean_nat_dec_lt(v___x_4661_, v_size_4655_);
lean_dec(v___x_4661_);
if (v___x_4662_ == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
lean_dec(v_r_4659_);
lean_dec(v_l_4658_);
lean_dec(v_v_4657_);
lean_dec(v_k_4656_);
v___x_4663_ = lean_nat_add(v___x_4653_, v_size_4654_);
v___x_4664_ = lean_nat_add(v___x_4663_, v_size_4655_);
lean_dec(v_size_4655_);
lean_dec(v___x_4663_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v_impl_4652_);
lean_ctor_set(v___x_4509_, 0, v___x_4664_);
v___x_4666_ = v___x_4509_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4667_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4667_, 3, v_l_4506_);
lean_ctor_set(v_reuseFailAlloc_4667_, 4, v_impl_4652_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
else
{
lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4731_; 
v_isSharedCheck_4731_ = !lean_is_exclusive(v_impl_4652_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; 
v_unused_4732_ = lean_ctor_get(v_impl_4652_, 4);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_impl_4652_, 3);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_impl_4652_, 2);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_impl_4652_, 1);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_impl_4652_, 0);
lean_dec(v_unused_4736_);
v___x_4669_ = v_impl_4652_;
v_isShared_4670_ = v_isSharedCheck_4731_;
goto v_resetjp_4668_;
}
else
{
lean_dec(v_impl_4652_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4731_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v_size_4671_; lean_object* v_k_4672_; lean_object* v_v_4673_; lean_object* v_l_4674_; lean_object* v_r_4675_; lean_object* v_size_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v_size_4671_ = lean_ctor_get(v_l_4658_, 0);
v_k_4672_ = lean_ctor_get(v_l_4658_, 1);
v_v_4673_ = lean_ctor_get(v_l_4658_, 2);
v_l_4674_ = lean_ctor_get(v_l_4658_, 3);
v_r_4675_ = lean_ctor_get(v_l_4658_, 4);
v_size_4676_ = lean_ctor_get(v_r_4659_, 0);
v___x_4677_ = lean_unsigned_to_nat(2u);
v___x_4678_ = lean_nat_mul(v___x_4677_, v_size_4676_);
v___x_4679_ = lean_nat_dec_lt(v_size_4671_, v___x_4678_);
lean_dec(v___x_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4707_; 
lean_inc(v_r_4675_);
lean_inc(v_l_4674_);
lean_inc(v_v_4673_);
lean_inc(v_k_4672_);
v_isSharedCheck_4707_ = !lean_is_exclusive(v_l_4658_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; lean_object* v_unused_4709_; lean_object* v_unused_4710_; lean_object* v_unused_4711_; lean_object* v_unused_4712_; 
v_unused_4708_ = lean_ctor_get(v_l_4658_, 4);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_l_4658_, 3);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_l_4658_, 2);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_l_4658_, 1);
lean_dec(v_unused_4711_);
v_unused_4712_ = lean_ctor_get(v_l_4658_, 0);
lean_dec(v_unused_4712_);
v___x_4681_ = v_l_4658_;
v_isShared_4682_ = v_isSharedCheck_4707_;
goto v_resetjp_4680_;
}
else
{
lean_dec(v_l_4658_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4707_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4697_; 
v___x_4683_ = lean_nat_add(v___x_4653_, v_size_4654_);
v___x_4684_ = lean_nat_add(v___x_4683_, v_size_4655_);
lean_dec(v_size_4655_);
if (lean_obj_tag(v_l_4674_) == 0)
{
lean_object* v_size_4705_; 
v_size_4705_ = lean_ctor_get(v_l_4674_, 0);
lean_inc(v_size_4705_);
v___y_4697_ = v_size_4705_;
goto v___jp_4696_;
}
else
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_unsigned_to_nat(0u);
v___y_4697_ = v___x_4706_;
goto v___jp_4696_;
}
v___jp_4685_:
{
lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4689_ = lean_nat_add(v___y_4686_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec(v___y_4686_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 4, v_r_4659_);
lean_ctor_set(v___x_4681_, 3, v_r_4675_);
lean_ctor_set(v___x_4681_, 2, v_v_4657_);
lean_ctor_set(v___x_4681_, 1, v_k_4656_);
lean_ctor_set(v___x_4681_, 0, v___x_4689_);
v___x_4691_ = v___x_4681_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v_k_4656_);
lean_ctor_set(v_reuseFailAlloc_4695_, 2, v_v_4657_);
lean_ctor_set(v_reuseFailAlloc_4695_, 3, v_r_4675_);
lean_ctor_set(v_reuseFailAlloc_4695_, 4, v_r_4659_);
v___x_4691_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
lean_object* v___x_4693_; 
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 4, v___x_4691_);
lean_ctor_set(v___x_4669_, 3, v___y_4687_);
lean_ctor_set(v___x_4669_, 2, v_v_4673_);
lean_ctor_set(v___x_4669_, 1, v_k_4672_);
lean_ctor_set(v___x_4669_, 0, v___x_4684_);
v___x_4693_ = v___x_4669_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4684_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4694_, 3, v___y_4687_);
lean_ctor_set(v_reuseFailAlloc_4694_, 4, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
v___jp_4696_:
{
lean_object* v___x_4698_; lean_object* v___x_4700_; 
v___x_4698_ = lean_nat_add(v___x_4683_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec(v___x_4683_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v_l_4674_);
lean_ctor_set(v___x_4509_, 0, v___x_4698_);
v___x_4700_ = v___x_4509_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4704_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4704_, 3, v_l_4506_);
lean_ctor_set(v_reuseFailAlloc_4704_, 4, v_l_4674_);
v___x_4700_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
lean_object* v___x_4701_; 
v___x_4701_ = lean_nat_add(v___x_4653_, v_size_4676_);
if (lean_obj_tag(v_r_4675_) == 0)
{
lean_object* v_size_4702_; 
v_size_4702_ = lean_ctor_get(v_r_4675_, 0);
lean_inc(v_size_4702_);
v___y_4686_ = v___x_4701_;
v___y_4687_ = v___x_4700_;
v___y_4688_ = v_size_4702_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_unsigned_to_nat(0u);
v___y_4686_ = v___x_4701_;
v___y_4687_ = v___x_4700_;
v___y_4688_ = v___x_4703_;
goto v___jp_4685_;
}
}
}
}
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
lean_del_object(v___x_4509_);
v___x_4713_ = lean_nat_add(v___x_4653_, v_size_4654_);
v___x_4714_ = lean_nat_add(v___x_4713_, v_size_4655_);
lean_dec(v_size_4655_);
v___x_4715_ = lean_nat_add(v___x_4713_, v_size_4671_);
lean_dec(v___x_4713_);
lean_inc_ref(v_l_4506_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 4, v_l_4658_);
lean_ctor_set(v___x_4669_, 3, v_l_4506_);
lean_ctor_set(v___x_4669_, 2, v_v_4505_);
lean_ctor_set(v___x_4669_, 1, v_k_4504_);
lean_ctor_set(v___x_4669_, 0, v___x_4715_);
v___x_4717_ = v___x_4669_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_l_4506_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_l_4658_);
v___x_4717_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
v_isSharedCheck_4724_ = !lean_is_exclusive(v_l_4506_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; 
v_unused_4725_ = lean_ctor_get(v_l_4506_, 4);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_l_4506_, 3);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_l_4506_, 2);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_l_4506_, 1);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_l_4506_, 0);
lean_dec(v_unused_4729_);
v___x_4719_ = v_l_4506_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_dec(v_l_4506_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 4, v_r_4659_);
lean_ctor_set(v___x_4719_, 3, v___x_4717_);
lean_ctor_set(v___x_4719_, 2, v_v_4657_);
lean_ctor_set(v___x_4719_, 1, v_k_4656_);
lean_ctor_set(v___x_4719_, 0, v___x_4714_);
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_k_4656_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_v_4657_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v_r_4659_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4737_; 
v_l_4737_ = lean_ctor_get(v_impl_4652_, 3);
lean_inc(v_l_4737_);
if (lean_obj_tag(v_l_4737_) == 0)
{
lean_object* v_r_4738_; lean_object* v_k_4739_; lean_object* v_v_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4763_; 
v_r_4738_ = lean_ctor_get(v_impl_4652_, 4);
v_k_4739_ = lean_ctor_get(v_impl_4652_, 1);
v_v_4740_ = lean_ctor_get(v_impl_4652_, 2);
v_isSharedCheck_4763_ = !lean_is_exclusive(v_impl_4652_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; lean_object* v_unused_4765_; 
v_unused_4764_ = lean_ctor_get(v_impl_4652_, 3);
lean_dec(v_unused_4764_);
v_unused_4765_ = lean_ctor_get(v_impl_4652_, 0);
lean_dec(v_unused_4765_);
v___x_4742_ = v_impl_4652_;
v_isShared_4743_ = v_isSharedCheck_4763_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_r_4738_);
lean_inc(v_v_4740_);
lean_inc(v_k_4739_);
lean_dec(v_impl_4652_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4763_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_k_4744_; lean_object* v_v_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4759_; 
v_k_4744_ = lean_ctor_get(v_l_4737_, 1);
v_v_4745_ = lean_ctor_get(v_l_4737_, 2);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_l_4737_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; lean_object* v_unused_4761_; lean_object* v_unused_4762_; 
v_unused_4760_ = lean_ctor_get(v_l_4737_, 4);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_l_4737_, 3);
lean_dec(v_unused_4761_);
v_unused_4762_ = lean_ctor_get(v_l_4737_, 0);
lean_dec(v_unused_4762_);
v___x_4747_ = v_l_4737_;
v_isShared_4748_ = v_isSharedCheck_4759_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_v_4745_);
lean_inc(v_k_4744_);
lean_dec(v_l_4737_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4759_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4751_; 
v___x_4749_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4738_, 2);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 4, v_r_4738_);
lean_ctor_set(v___x_4747_, 3, v_r_4738_);
lean_ctor_set(v___x_4747_, 2, v_v_4505_);
lean_ctor_set(v___x_4747_, 1, v_k_4504_);
lean_ctor_set(v___x_4747_, 0, v___x_4653_);
v___x_4751_ = v___x_4747_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4758_, 3, v_r_4738_);
lean_ctor_set(v_reuseFailAlloc_4758_, 4, v_r_4738_);
v___x_4751_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4753_; 
lean_inc(v_r_4738_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 3, v_r_4738_);
lean_ctor_set(v___x_4742_, 0, v___x_4653_);
v___x_4753_ = v___x_4742_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_k_4739_);
lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_v_4740_);
lean_ctor_set(v_reuseFailAlloc_4757_, 3, v_r_4738_);
lean_ctor_set(v_reuseFailAlloc_4757_, 4, v_r_4738_);
v___x_4753_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4755_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v___x_4753_);
lean_ctor_set(v___x_4509_, 3, v___x_4751_);
lean_ctor_set(v___x_4509_, 2, v_v_4745_);
lean_ctor_set(v___x_4509_, 1, v_k_4744_);
lean_ctor_set(v___x_4509_, 0, v___x_4749_);
v___x_4755_ = v___x_4509_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_k_4744_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_v_4745_);
lean_ctor_set(v_reuseFailAlloc_4756_, 3, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4756_, 4, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
}
else
{
lean_object* v_r_4766_; 
v_r_4766_ = lean_ctor_get(v_impl_4652_, 4);
lean_inc(v_r_4766_);
if (lean_obj_tag(v_r_4766_) == 0)
{
lean_object* v_k_4767_; lean_object* v_v_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4779_; 
v_k_4767_ = lean_ctor_get(v_impl_4652_, 1);
v_v_4768_ = lean_ctor_get(v_impl_4652_, 2);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_impl_4652_);
if (v_isSharedCheck_4779_ == 0)
{
lean_object* v_unused_4780_; lean_object* v_unused_4781_; lean_object* v_unused_4782_; 
v_unused_4780_ = lean_ctor_get(v_impl_4652_, 4);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v_impl_4652_, 3);
lean_dec(v_unused_4781_);
v_unused_4782_ = lean_ctor_get(v_impl_4652_, 0);
lean_dec(v_unused_4782_);
v___x_4770_ = v_impl_4652_;
v_isShared_4771_ = v_isSharedCheck_4779_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_v_4768_);
lean_inc(v_k_4767_);
lean_dec(v_impl_4652_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4779_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4772_ = lean_unsigned_to_nat(3u);
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 4, v_l_4737_);
lean_ctor_set(v___x_4770_, 2, v_v_4505_);
lean_ctor_set(v___x_4770_, 1, v_k_4504_);
lean_ctor_set(v___x_4770_, 0, v___x_4653_);
v___x_4774_ = v___x_4770_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_l_4737_);
lean_ctor_set(v_reuseFailAlloc_4778_, 4, v_l_4737_);
v___x_4774_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4776_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v_r_4766_);
lean_ctor_set(v___x_4509_, 3, v___x_4774_);
lean_ctor_set(v___x_4509_, 2, v_v_4768_);
lean_ctor_set(v___x_4509_, 1, v_k_4767_);
lean_ctor_set(v___x_4509_, 0, v___x_4772_);
v___x_4776_ = v___x_4509_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4772_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_k_4767_);
lean_ctor_set(v_reuseFailAlloc_4777_, 2, v_v_4768_);
lean_ctor_set(v_reuseFailAlloc_4777_, 3, v___x_4774_);
lean_ctor_set(v_reuseFailAlloc_4777_, 4, v_r_4766_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4783_ = lean_unsigned_to_nat(2u);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 4, v_impl_4652_);
lean_ctor_set(v___x_4509_, 3, v_r_4766_);
lean_ctor_set(v___x_4509_, 0, v___x_4783_);
v___x_4785_ = v___x_4509_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_r_4766_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v_impl_4652_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
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
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = lean_unsigned_to_nat(1u);
v___x_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
lean_ctor_set(v___x_4789_, 1, v_k_4500_);
lean_ctor_set(v___x_4789_, 2, v_v_4501_);
lean_ctor_set(v___x_4789_, 3, v_t_4502_);
lean_ctor_set(v___x_4789_, 4, v_t_4502_);
return v___x_4789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4790_, lean_object* v_k_4791_){
_start:
{
if (lean_obj_tag(v_t_4790_) == 0)
{
lean_object* v_k_4792_; lean_object* v_v_4793_; lean_object* v_l_4794_; lean_object* v_r_4795_; uint8_t v___x_4796_; 
v_k_4792_ = lean_ctor_get(v_t_4790_, 1);
v_v_4793_ = lean_ctor_get(v_t_4790_, 2);
v_l_4794_ = lean_ctor_get(v_t_4790_, 3);
v_r_4795_ = lean_ctor_get(v_t_4790_, 4);
v___x_4796_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4791_, v_k_4792_);
switch(v___x_4796_)
{
case 0:
{
v_t_4790_ = v_l_4794_;
goto _start;
}
case 1:
{
lean_object* v___x_4798_; 
lean_inc(v_v_4793_);
v___x_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4798_, 0, v_v_4793_);
return v___x_4798_;
}
default: 
{
v_t_4790_ = v_r_4795_;
goto _start;
}
}
}
else
{
lean_object* v___x_4800_; 
v___x_4800_ = lean_box(0);
return v___x_4800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4801_, lean_object* v_k_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4801_, v_k_4802_);
lean_dec(v_k_4802_);
lean_dec(v_t_4801_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4804_, lean_object* v_k_4805_, lean_object* v_v_4806_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4804_, v_k_4805_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4808_ = lean_box(0);
v___x_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4809_, 0, v_v_4806_);
lean_ctor_set(v___x_4809_, 1, v___x_4808_);
v___x_4810_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4805_, v___x_4809_, v_map_4804_);
return v___x_4810_;
}
else
{
lean_object* v_val_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_val_4811_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_val_4811_);
lean_dec_ref_known(v___x_4807_, 1);
v___x_4812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4812_, 0, v_v_4806_);
lean_ctor_set(v___x_4812_, 1, v_val_4811_);
v___x_4813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4805_, v___x_4812_, v_map_4804_);
return v___x_4813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4814_, lean_object* v_map_4815_, lean_object* v_k_4816_, lean_object* v_v_4817_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4815_, v_k_4816_, v_v_4817_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4819_, lean_object* v_t_4820_, lean_object* v_k_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4820_, v_k_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4823_, lean_object* v_t_4824_, lean_object* v_k_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4823_, v_t_4824_, v_k_4825_);
lean_dec(v_k_4825_);
lean_dec(v_t_4824_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4827_, lean_object* v_k_4828_, lean_object* v_v_4829_, lean_object* v_t_4830_, lean_object* v_hl_4831_){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4828_, v_v_4829_, v_t_4830_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4833_){
_start:
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_box(1);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4835_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = lean_box(1);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4837_, lean_object* v_a_4838_, lean_object* v_b_4839_, lean_object* v_c_4840_){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4841_, 0, v_a_4838_);
lean_ctor_set(v___x_4841_, 1, v_b_4839_);
v___x_4842_ = lean_apply_2(v_f_4837_, v___x_4841_, v_c_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4843_, lean_object* v_____do__lift_4844_){
_start:
{
lean_object* v_a_4845_; lean_object* v___x_4846_; 
v_a_4845_ = lean_ctor_get(v_____do__lift_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref(v_____do__lift_4844_);
v___x_4846_ = lean_apply_2(v_toPure_4843_, lean_box(0), v_a_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4847_, lean_object* v_m_4848_, lean_object* v_init_4849_, lean_object* v_f_4850_){
_start:
{
lean_object* v_toApplicative_4851_; lean_object* v_toBind_4852_; lean_object* v_toPure_4853_; lean_object* v___f_4854_; lean_object* v___x_4855_; lean_object* v___f_4856_; lean_object* v___x_4857_; 
v_toApplicative_4851_ = lean_ctor_get(v_inst_4847_, 0);
v_toBind_4852_ = lean_ctor_get(v_inst_4847_, 1);
lean_inc(v_toBind_4852_);
v_toPure_4853_ = lean_ctor_get(v_toApplicative_4851_, 1);
lean_inc(v_toPure_4853_);
v___f_4854_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4854_, 0, v_f_4850_);
v___x_4855_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4847_, v___f_4854_, v_init_4849_, v_m_4848_);
v___f_4856_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4856_, 0, v_toPure_4853_);
v___x_4857_ = lean_apply_4(v_toBind_4852_, lean_box(0), lean_box(0), v___x_4855_, v___f_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4858_, lean_object* v_00_u03b1_4859_, lean_object* v_inst_4860_, lean_object* v_00_u03b2_4861_, lean_object* v_m_4862_, lean_object* v_init_4863_, lean_object* v_f_4864_){
_start:
{
lean_object* v_toApplicative_4865_; lean_object* v_toBind_4866_; lean_object* v_toPure_4867_; lean_object* v___f_4868_; lean_object* v___x_4869_; lean_object* v___f_4870_; lean_object* v___x_4871_; 
v_toApplicative_4865_ = lean_ctor_get(v_inst_4860_, 0);
v_toBind_4866_ = lean_ctor_get(v_inst_4860_, 1);
lean_inc(v_toBind_4866_);
v_toPure_4867_ = lean_ctor_get(v_toApplicative_4865_, 1);
lean_inc(v_toPure_4867_);
v___f_4868_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4868_, 0, v_f_4864_);
v___x_4869_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4860_, v___f_4868_, v_init_4863_, v_m_4862_);
v___f_4870_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4870_, 0, v_toPure_4867_);
v___x_4871_ = lean_apply_4(v_toBind_4866_, lean_box(0), lean_box(0), v___x_4869_, v___f_4870_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4872_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4873_, 0, lean_box(0));
lean_closure_set(v___x_4873_, 1, lean_box(0));
lean_closure_set(v___x_4873_, 2, v_inst_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4874_, lean_object* v_00_u03b1_4875_, lean_object* v_inst_4876_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4877_, 0, lean_box(0));
lean_closure_set(v___x_4877_, 1, lean_box(0));
lean_closure_set(v___x_4877_, 2, v_inst_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t v_x_4882_){
_start:
{
switch(v_x_4882_)
{
case 0:
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_unsigned_to_nat(0u);
return v___x_4883_;
}
case 1:
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_unsigned_to_nat(1u);
return v___x_4884_;
}
default: 
{
lean_object* v___x_4885_; 
v___x_4885_ = lean_unsigned_to_nat(2u);
return v___x_4885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object* v_x_4886_){
_start:
{
uint8_t v_x_boxed_4887_; lean_object* v_res_4888_; 
v_x_boxed_4887_ = lean_unbox(v_x_4886_);
v_res_4888_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_boxed_4887_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4889_){
_start:
{
lean_inc(v_k_4889_);
return v_k_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4890_);
lean_dec(v_k_4890_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4892_, lean_object* v_ctorIdx_4893_, uint8_t v_t_4894_, lean_object* v_h_4895_, lean_object* v_k_4896_){
_start:
{
lean_inc(v_k_4896_);
return v_k_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4897_, lean_object* v_ctorIdx_4898_, lean_object* v_t_4899_, lean_object* v_h_4900_, lean_object* v_k_4901_){
_start:
{
uint8_t v_t_boxed_4902_; lean_object* v_res_4903_; 
v_t_boxed_4902_ = lean_unbox(v_t_4899_);
v_res_4903_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4897_, v_ctorIdx_4898_, v_t_boxed_4902_, v_h_4900_, v_k_4901_);
lean_dec(v_k_4901_);
lean_dec(v_ctorIdx_4898_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4904_){
_start:
{
lean_inc(v_default_4904_);
return v_default_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4905_);
lean_dec(v_default_4905_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4907_, uint8_t v_t_4908_, lean_object* v_h_4909_, lean_object* v_default_4910_){
_start:
{
lean_inc(v_default_4910_);
return v_default_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4911_, lean_object* v_t_4912_, lean_object* v_h_4913_, lean_object* v_default_4914_){
_start:
{
uint8_t v_t_boxed_4915_; lean_object* v_res_4916_; 
v_t_boxed_4915_ = lean_unbox(v_t_4912_);
v_res_4916_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4911_, v_t_boxed_4915_, v_h_4913_, v_default_4914_);
lean_dec(v_default_4914_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4917_){
_start:
{
lean_inc(v_symbol_4917_);
return v_symbol_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4918_);
lean_dec(v_symbol_4918_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4920_, uint8_t v_t_4921_, lean_object* v_h_4922_, lean_object* v_symbol_4923_){
_start:
{
lean_inc(v_symbol_4923_);
return v_symbol_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4924_, lean_object* v_t_4925_, lean_object* v_h_4926_, lean_object* v_symbol_4927_){
_start:
{
uint8_t v_t_boxed_4928_; lean_object* v_res_4929_; 
v_t_boxed_4928_ = lean_unbox(v_t_4925_);
v_res_4929_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4924_, v_t_boxed_4928_, v_h_4926_, v_symbol_4927_);
lean_dec(v_symbol_4927_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4930_){
_start:
{
lean_inc(v_both_4930_);
return v_both_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4931_);
lean_dec(v_both_4931_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4933_, uint8_t v_t_4934_, lean_object* v_h_4935_, lean_object* v_both_4936_){
_start:
{
lean_inc(v_both_4936_);
return v_both_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4937_, lean_object* v_t_4938_, lean_object* v_h_4939_, lean_object* v_both_4940_){
_start:
{
uint8_t v_t_boxed_4941_; lean_object* v_res_4942_; 
v_t_boxed_4941_ = lean_unbox(v_t_4938_);
v_res_4942_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4937_, v_t_boxed_4941_, v_h_4939_, v_both_4940_);
lean_dec(v_both_4940_);
return v_res_4942_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4943_; 
v___x_4943_ = 0;
return v___x_4943_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4944_; 
v___x_4944_ = 0;
return v___x_4944_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4945_, uint8_t v_y_4946_){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4947_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4945_);
v___x_4948_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_y_4946_);
v___x_4949_ = lean_nat_dec_eq(v___x_4947_, v___x_4948_);
lean_dec(v___x_4948_);
lean_dec(v___x_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4950_, lean_object* v_y_4951_){
_start:
{
uint8_t v_x_21__boxed_4952_; uint8_t v_y_22__boxed_4953_; uint8_t v_res_4954_; lean_object* v_r_4955_; 
v_x_21__boxed_4952_ = lean_unbox(v_x_4950_);
v_y_22__boxed_4953_ = lean_unbox(v_y_4951_);
v_res_4954_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_21__boxed_4952_, v_y_22__boxed_4953_);
v_r_4955_ = lean_box(v_res_4954_);
return v_r_4955_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4967_ = lean_unsigned_to_nat(2u);
v___x_4968_ = lean_nat_to_int(v___x_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4969_, lean_object* v_prec_4970_){
_start:
{
lean_object* v___y_4972_; lean_object* v___y_4979_; lean_object* v___y_4986_; 
switch(v_x_4969_)
{
case 0:
{
lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4992_ = lean_unsigned_to_nat(1024u);
v___x_4993_ = lean_nat_dec_le(v___x_4992_, v_prec_4970_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; 
v___x_4994_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4972_ = v___x_4994_;
goto v___jp_4971_;
}
else
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4972_ = v___x_4995_;
goto v___jp_4971_;
}
}
case 1:
{
lean_object* v___x_4996_; uint8_t v___x_4997_; 
v___x_4996_ = lean_unsigned_to_nat(1024u);
v___x_4997_ = lean_nat_dec_le(v___x_4996_, v_prec_4970_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
v___x_4998_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4979_ = v___x_4998_;
goto v___jp_4978_;
}
else
{
lean_object* v___x_4999_; 
v___x_4999_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4979_ = v___x_4999_;
goto v___jp_4978_;
}
}
default: 
{
lean_object* v___x_5000_; uint8_t v___x_5001_; 
v___x_5000_ = lean_unsigned_to_nat(1024u);
v___x_5001_ = lean_nat_dec_le(v___x_5000_, v_prec_4970_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; 
v___x_5002_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4986_ = v___x_5002_;
goto v___jp_4985_;
}
else
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4986_ = v___x_5003_;
goto v___jp_4985_;
}
}
}
v___jp_4971_:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; uint8_t v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4973_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_4972_);
v___x_4974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___y_4972_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = 0;
v___x_4976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4976_, 0, v___x_4974_);
lean_ctor_set_uint8(v___x_4976_, sizeof(void*)*1, v___x_4975_);
v___x_4977_ = l_Repr_addAppParen(v___x_4976_, v_prec_4970_);
return v___x_4977_;
}
v___jp_4978_:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4980_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_4979_);
v___x_4981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___y_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = 0;
v___x_4983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4983_, 0, v___x_4981_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*1, v___x_4982_);
v___x_4984_ = l_Repr_addAppParen(v___x_4983_, v_prec_4970_);
return v___x_4984_;
}
v___jp_4985_:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; uint8_t v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4987_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_4986_);
v___x_4988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___y_4986_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
v___x_4989_ = 0;
v___x_4990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*1, v___x_4989_);
v___x_4991_ = l_Repr_addAppParen(v___x_4990_, v_prec_4970_);
return v___x_4991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_5004_, lean_object* v_prec_5005_){
_start:
{
uint8_t v_x_169__boxed_5006_; lean_object* v_res_5007_; 
v_x_169__boxed_5006_ = lean_unbox(v_x_5004_);
v_res_5007_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_169__boxed_5006_, v_prec_5005_);
lean_dec(v_prec_5005_);
return v_res_5007_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_5010_; 
v___x_5010_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5010_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
return v___x_5012_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5013_ = 0;
v___x_5014_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_5015_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_5016_ = lean_box(0);
v___x_5017_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
lean_ctor_set(v___x_5017_, 1, v___x_5015_);
lean_ctor_set(v___x_5017_, 2, v___x_5014_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*3, v___x_5013_);
return v___x_5017_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_5018_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_5019_; 
v___x_5019_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_5020_, lean_object* v_c_5021_, lean_object* v_s_5022_, uint8_t v_behavior_5023_){
_start:
{
lean_object* v___x_5024_; lean_object* v_fst_5025_; lean_object* v_snd_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5068_; 
v___x_5024_ = l_Lean_Parser_peekToken(v_c_5021_, v_s_5022_);
v_fst_5025_ = lean_ctor_get(v___x_5024_, 0);
v_snd_5026_ = lean_ctor_get(v___x_5024_, 1);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5028_ = v___x_5024_;
v_isShared_5029_ = v_isSharedCheck_5068_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_snd_5026_);
lean_inc(v_fst_5025_);
lean_dec(v___x_5024_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5068_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v_n_5031_; 
if (lean_obj_tag(v_snd_5026_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
lean_del_object(v___x_5028_);
lean_dec(v_fst_5025_);
v_a_5043_ = lean_ctor_get(v_snd_5026_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v_snd_5026_, 1);
v___x_5044_ = lean_box(0);
v___x_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5045_, 0, v_a_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
return v___x_5045_;
}
else
{
lean_object* v_a_5046_; 
v_a_5046_ = lean_ctor_get(v_snd_5026_, 0);
lean_inc(v_a_5046_);
lean_dec_ref_known(v_snd_5026_, 1);
switch(lean_obj_tag(v_a_5046_))
{
case 2:
{
lean_object* v_val_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v_val_5047_ = lean_ctor_get(v_a_5046_, 1);
lean_inc_ref(v_val_5047_);
lean_dec_ref_known(v_a_5046_, 2);
v___x_5048_ = lean_box(0);
v___x_5049_ = l_Lean_Name_str___override(v___x_5048_, v_val_5047_);
v_n_5031_ = v___x_5049_;
goto v___jp_5030_;
}
case 3:
{
switch(v_behavior_5023_)
{
case 0:
{
lean_dec_ref_known(v_a_5046_, 4);
goto v___jp_5041_;
}
case 1:
{
lean_object* v_val_5050_; lean_object* v___x_5051_; 
v_val_5050_ = lean_ctor_get(v_a_5046_, 2);
lean_inc(v_val_5050_);
lean_dec_ref_known(v_a_5046_, 4);
v___x_5051_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5020_, v_val_5050_);
lean_dec(v_val_5050_);
if (lean_obj_tag(v___x_5051_) == 0)
{
goto v___jp_5041_;
}
else
{
lean_object* v_val_5052_; lean_object* v___x_5053_; 
lean_del_object(v___x_5028_);
v_val_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_val_5052_);
lean_dec_ref_known(v___x_5051_, 1);
v___x_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5053_, 0, v_fst_5025_);
lean_ctor_set(v___x_5053_, 1, v_val_5052_);
return v___x_5053_;
}
}
default: 
{
lean_object* v_val_5054_; lean_object* v___x_5055_; 
v_val_5054_ = lean_ctor_get(v_a_5046_, 2);
lean_inc(v_val_5054_);
lean_dec_ref_known(v_a_5046_, 4);
v___x_5055_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5020_, v_val_5054_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_dec(v_val_5054_);
goto v___jp_5041_;
}
else
{
lean_object* v_val_5056_; lean_object* v___x_5057_; uint8_t v___x_5058_; 
lean_del_object(v___x_5028_);
v_val_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_val_5056_);
lean_dec_ref_known(v___x_5055_, 1);
v___x_5057_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_5058_ = lean_name_eq(v_val_5054_, v___x_5057_);
lean_dec(v_val_5054_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5020_, v___x_5057_);
if (lean_obj_tag(v___x_5059_) == 1)
{
lean_object* v_val_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v_val_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_val_5060_);
lean_dec_ref_known(v___x_5059_, 1);
v___x_5061_ = l_List_appendTR___redArg(v_val_5056_, v_val_5060_);
v___x_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5062_, 0, v_fst_5025_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
return v___x_5062_;
}
else
{
lean_object* v___x_5063_; 
lean_dec(v___x_5059_);
v___x_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5063_, 0, v_fst_5025_);
lean_ctor_set(v___x_5063_, 1, v_val_5056_);
return v___x_5063_;
}
}
else
{
lean_object* v___x_5064_; 
v___x_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5064_, 0, v_fst_5025_);
lean_ctor_set(v___x_5064_, 1, v_val_5056_);
return v___x_5064_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_5065_; 
v_kind_5065_ = lean_ctor_get(v_a_5046_, 1);
lean_inc(v_kind_5065_);
lean_dec_ref_known(v_a_5046_, 3);
v_n_5031_ = v_kind_5065_;
goto v___jp_5030_;
}
default: 
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
lean_dec(v_a_5046_);
lean_del_object(v___x_5028_);
v___x_5066_ = lean_box(0);
v___x_5067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5067_, 0, v_fst_5025_);
lean_ctor_set(v___x_5067_, 1, v___x_5066_);
return v___x_5067_;
}
}
}
v___jp_5030_:
{
lean_object* v___x_5032_; 
v___x_5032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5020_, v_n_5031_);
lean_dec(v_n_5031_);
if (lean_obj_tag(v___x_5032_) == 1)
{
lean_object* v_val_5033_; lean_object* v___x_5035_; 
v_val_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_val_5033_);
lean_dec_ref_known(v___x_5032_, 1);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 1, v_val_5033_);
v___x_5035_ = v___x_5028_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_fst_5025_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_val_5033_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5039_; 
lean_dec(v___x_5032_);
v___x_5037_ = lean_box(0);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 1, v___x_5037_);
v___x_5039_ = v___x_5028_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_fst_5025_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
v___jp_5041_:
{
lean_object* v___x_5042_; 
v___x_5042_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_5031_ = v___x_5042_;
goto v___jp_5030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_5069_, lean_object* v_c_5070_, lean_object* v_s_5071_, lean_object* v_behavior_5072_){
_start:
{
uint8_t v_behavior_boxed_5073_; lean_object* v_res_5074_; 
v_behavior_boxed_5073_ = lean_unbox(v_behavior_5072_);
v_res_5074_ = l_Lean_Parser_indexed___redArg(v_map_5069_, v_c_5070_, v_s_5071_, v_behavior_boxed_5073_);
lean_dec(v_map_5069_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_5075_, lean_object* v_map_5076_, lean_object* v_c_5077_, lean_object* v_s_5078_, uint8_t v_behavior_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_Parser_indexed___redArg(v_map_5076_, v_c_5077_, v_s_5078_, v_behavior_5079_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_5081_, lean_object* v_map_5082_, lean_object* v_c_5083_, lean_object* v_s_5084_, lean_object* v_behavior_5085_){
_start:
{
uint8_t v_behavior_boxed_5086_; lean_object* v_res_5087_; 
v_behavior_boxed_5086_ = lean_unbox(v_behavior_5085_);
v_res_5087_ = l_Lean_Parser_indexed(v_00_u03b1_5081_, v_map_5082_, v_c_5083_, v_s_5084_, v_behavior_boxed_5086_);
lean_dec(v_map_5082_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lean_Parser_whitespace(v___y_5089_, v___y_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_5092_, v___y_5093_, v___y_5094_);
lean_dec(v_x_5092_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___f_5098_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_5099_ = lean_st_mk_ref(v___f_5098_);
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_5103_){
_start:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_st_ref_get(v___x_5103_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_5107_);
lean_dec(v___x_5107_);
return v_res_5109_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5110_; lean_object* v___f_5111_; 
v___x_5110_ = l_Lean_Parser_categoryParserFnRef;
v___f_5111_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5111_, 0, v___x_5110_);
return v___f_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___f_5113_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_5114_ = lean_box(0);
v___x_5115_ = lean_box(2);
v___x_5116_ = l_Lean_registerEnvExtension___redArg(v___f_5113_, v___x_5114_, v___x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v___x_5122_; 
v___x_5122_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_5120_, v___y_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_5123_, v___y_5124_, v___y_5125_);
lean_dec_ref(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v_a_5123_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_5130_, lean_object* v_ctx_5131_, lean_object* v_s_5132_){
_start:
{
lean_object* v_toParserModuleContext_5133_; lean_object* v_env_5134_; lean_object* v___x_5135_; lean_object* v_asyncMode_5136_; lean_object* v___f_5137_; lean_object* v___x_5138_; lean_object* v___x_11__overap_5139_; lean_object* v___x_5140_; 
v_toParserModuleContext_5133_ = lean_ctor_get(v_ctx_5131_, 1);
v_env_5134_ = lean_ctor_get(v_toParserModuleContext_5133_, 0);
v___x_5135_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_5136_ = lean_ctor_get(v___x_5135_, 2);
v___f_5137_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_5138_ = lean_box(0);
lean_inc_ref(v_env_5134_);
v___x_11__overap_5139_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_5137_, v___x_5135_, v_env_5134_, v_asyncMode_5136_, v___x_5138_);
v___x_5140_ = lean_apply_3(v___x_11__overap_5139_, v_catName_5130_, v_ctx_5131_, v_s_5132_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_5141_, lean_object* v_x_5142_){
_start:
{
lean_object* v_quotDepth_5143_; uint8_t v_suppressInsideQuot_5144_; lean_object* v_savedPos_x3f_5145_; lean_object* v_forbiddenTks_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
v_quotDepth_5143_ = lean_ctor_get(v_x_5142_, 1);
v_suppressInsideQuot_5144_ = lean_ctor_get_uint8(v_x_5142_, sizeof(void*)*4);
v_savedPos_x3f_5145_ = lean_ctor_get(v_x_5142_, 2);
v_forbiddenTks_5146_ = lean_ctor_get(v_x_5142_, 3);
v_isSharedCheck_5153_ = !lean_is_exclusive(v_x_5142_);
if (v_isSharedCheck_5153_ == 0)
{
lean_object* v_unused_5154_; 
v_unused_5154_ = lean_ctor_get(v_x_5142_, 0);
lean_dec(v_unused_5154_);
v___x_5148_ = v_x_5142_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_forbiddenTks_5146_);
lean_inc(v_savedPos_x3f_5145_);
lean_inc(v_quotDepth_5143_);
lean_dec(v_x_5142_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 0, v_prec_5141_);
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_prec_5141_);
lean_ctor_set(v_reuseFailAlloc_5152_, 1, v_quotDepth_5143_);
lean_ctor_set(v_reuseFailAlloc_5152_, 2, v_savedPos_x3f_5145_);
lean_ctor_set(v_reuseFailAlloc_5152_, 3, v_forbiddenTks_5146_);
lean_ctor_set_uint8(v_reuseFailAlloc_5152_, sizeof(void*)*4, v_suppressInsideQuot_5144_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_5155_, lean_object* v_prec_5156_){
_start:
{
lean_object* v___f_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___f_5157_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_5157_, 0, v_prec_5156_);
v___x_5158_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_5155_);
v___x_5159_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_5159_, 0, v_catName_5155_);
v___x_5160_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_5160_, 0, v_catName_5155_);
lean_closure_set(v___x_5160_, 1, v___x_5159_);
v___x_5161_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5161_, 0, v___f_5157_);
lean_closure_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5158_);
lean_ctor_set(v___x_5162_, 1, v___x_5161_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5166_){
_start:
{
lean_object* v___x_5167_; lean_object* v___x_5168_; 
v___x_5167_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5168_ = l_Lean_Parser_categoryParser(v___x_5167_, v_prec_5166_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5170_, lean_object* v_s_5171_){
_start:
{
lean_object* v_stxStack_5172_; lean_object* v_pos_5173_; lean_object* v_prev_5174_; uint8_t v___x_5175_; 
v_stxStack_5172_ = lean_ctor_get(v_s_5171_, 0);
v_pos_5173_ = lean_ctor_get(v_s_5171_, 2);
v_prev_5174_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5172_);
v___x_5175_ = l_Lean_Parser_checkTailNoWs(v_prev_5174_);
lean_dec(v_prev_5174_);
if (v___x_5175_ == 0)
{
return v_s_5171_;
}
else
{
lean_object* v_toInputContext_5176_; uint8_t v___x_5177_; 
v_toInputContext_5176_ = lean_ctor_get(v_c_5170_, 0);
v___x_5177_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5176_, v_pos_5173_);
if (v___x_5177_ == 0)
{
lean_object* v_inputString_5178_; uint32_t v_curr_5179_; uint32_t v___x_5180_; uint8_t v___x_5181_; 
v_inputString_5178_ = lean_ctor_get(v_toInputContext_5176_, 0);
v_curr_5179_ = lean_string_utf8_get_fast(v_inputString_5178_, v_pos_5173_);
v___x_5180_ = 58;
v___x_5181_ = lean_uint32_dec_eq(v_curr_5179_, v___x_5180_);
if (v___x_5181_ == 0)
{
return v_s_5171_;
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5182_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5183_ = lean_box(0);
v___x_5184_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5171_, v___x_5182_, v___x_5183_, v___x_5181_);
return v___x_5184_;
}
}
else
{
return v_s_5171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5185_, lean_object* v_s_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5185_, v_s_5186_);
lean_dec_ref(v_c_5185_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5200_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5201_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5202_ = l_Lean_addBuiltinDocString(v___x_5200_, v___x_5201_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5205_, lean_object* v_p_5206_, lean_object* v_c_5207_, lean_object* v_s_5208_){
_start:
{
lean_object* v___x_5209_; lean_object* v_errorMsg_5210_; 
v___x_5209_ = lean_apply_2(v_p_5206_, v_c_5207_, v_s_5208_);
v_errorMsg_5210_ = lean_ctor_get(v___x_5209_, 4);
lean_inc(v_errorMsg_5210_);
if (lean_obj_tag(v_errorMsg_5210_) == 1)
{
lean_object* v_val_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5241_; 
v_val_5211_ = lean_ctor_get(v_errorMsg_5210_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v_errorMsg_5210_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5213_ = v_errorMsg_5210_;
v_isShared_5214_ = v_isSharedCheck_5241_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_val_5211_);
lean_dec(v_errorMsg_5210_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5241_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v_stxStack_5215_; lean_object* v_lhsPrec_5216_; lean_object* v_pos_5217_; lean_object* v_cache_5218_; lean_object* v_recoveredErrors_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5239_; 
v_stxStack_5215_ = lean_ctor_get(v___x_5209_, 0);
v_lhsPrec_5216_ = lean_ctor_get(v___x_5209_, 1);
v_pos_5217_ = lean_ctor_get(v___x_5209_, 2);
v_cache_5218_ = lean_ctor_get(v___x_5209_, 3);
v_recoveredErrors_5219_ = lean_ctor_get(v___x_5209_, 5);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5239_ == 0)
{
lean_object* v_unused_5240_; 
v_unused_5240_ = lean_ctor_get(v___x_5209_, 4);
lean_dec(v_unused_5240_);
v___x_5221_ = v___x_5209_;
v_isShared_5222_ = v_isSharedCheck_5239_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_recoveredErrors_5219_);
lean_inc(v_cache_5218_);
lean_inc(v_pos_5217_);
lean_inc(v_lhsPrec_5216_);
lean_inc(v_stxStack_5215_);
lean_dec(v___x_5209_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5239_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v_unexpectedTk_5223_; lean_object* v_unexpected_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5237_; 
v_unexpectedTk_5223_ = lean_ctor_get(v_val_5211_, 0);
v_unexpected_5224_ = lean_ctor_get(v_val_5211_, 1);
v_isSharedCheck_5237_ = !lean_is_exclusive(v_val_5211_);
if (v_isSharedCheck_5237_ == 0)
{
lean_object* v_unused_5238_; 
v_unused_5238_ = lean_ctor_get(v_val_5211_, 2);
lean_dec(v_unused_5238_);
v___x_5226_ = v_val_5211_;
v_isShared_5227_ = v_isSharedCheck_5237_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_unexpected_5224_);
lean_inc(v_unexpectedTk_5223_);
lean_dec(v_val_5211_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5237_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 2, v_expected_5205_);
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_unexpectedTk_5223_);
lean_ctor_set(v_reuseFailAlloc_5236_, 1, v_unexpected_5224_);
lean_ctor_set(v_reuseFailAlloc_5236_, 2, v_expected_5205_);
v___x_5229_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
lean_object* v___x_5231_; 
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 0, v___x_5229_);
v___x_5231_ = v___x_5213_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v___x_5229_);
v___x_5231_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5233_; 
if (v_isShared_5222_ == 0)
{
lean_ctor_set(v___x_5221_, 4, v___x_5231_);
v___x_5233_ = v___x_5221_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_stxStack_5215_);
lean_ctor_set(v_reuseFailAlloc_5234_, 1, v_lhsPrec_5216_);
lean_ctor_set(v_reuseFailAlloc_5234_, 2, v_pos_5217_);
lean_ctor_set(v_reuseFailAlloc_5234_, 3, v_cache_5218_);
lean_ctor_set(v_reuseFailAlloc_5234_, 4, v___x_5231_);
lean_ctor_set(v_reuseFailAlloc_5234_, 5, v_recoveredErrors_5219_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5210_);
lean_dec(v_expected_5205_);
return v___x_5209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5242_, lean_object* v_p_5243_){
_start:
{
lean_object* v_info_5244_; lean_object* v_fn_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5253_; 
v_info_5244_ = lean_ctor_get(v_p_5243_, 0);
v_fn_5245_ = lean_ctor_get(v_p_5243_, 1);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_p_5243_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5247_ = v_p_5243_;
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_fn_5245_);
lean_inc(v_info_5244_);
lean_dec(v_p_5243_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
v___x_5249_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5249_, 0, v_expected_5242_);
lean_closure_set(v___x_5249_, 1, v_fn_5245_);
if (v_isShared_5248_ == 0)
{
lean_ctor_set(v___x_5247_, 1, v___x_5249_);
v___x_5251_ = v___x_5247_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_info_5244_);
lean_ctor_set(v_reuseFailAlloc_5252_, 1, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5254_, lean_object* v_s_5255_){
_start:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5256_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_5257_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5255_, v___x_5256_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5258_, lean_object* v_s_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_Lean_Parser_pushNone___lam__0(v_x_5258_, v_s_5259_);
lean_dec_ref(v_x_5258_);
return v_res_5260_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; 
v___x_5270_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5271_ = l_Lean_Parser_symbolNoAntiquot(v___x_5270_);
return v___x_5271_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = lean_unsigned_to_nat(0u);
v___x_5273_ = l_Lean_Parser_termParser(v___x_5272_);
return v___x_5273_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5275_ = l_Lean_Parser_decQuotDepth(v___x_5274_);
return v___x_5275_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5276_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5277_ = l_Lean_Parser_symbolNoAntiquot(v___x_5276_);
return v___x_5277_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v___x_5278_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5279_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5280_ = l_Lean_Parser_andthen(v___x_5279_, v___x_5278_);
return v___x_5280_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5281_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5282_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5283_ = l_Lean_Parser_andthen(v___x_5282_, v___x_5281_);
return v___x_5283_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5284_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5285_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5286_ = l_Lean_Parser_node(v___x_5285_, v___x_5284_);
return v___x_5286_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5287_; 
v___x_5287_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5287_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5290_ = l_Lean_Parser_symbolNoAntiquot(v___x_5289_);
return v___x_5290_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5291_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5292_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5293_ = l_Lean_Parser_orelse(v___x_5292_, v___x_5291_);
return v___x_5293_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5294_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5295_ = l_Lean_Parser_identNoAntiquot;
v___x_5296_ = l_Lean_Parser_orelse(v___x_5295_, v___x_5294_);
return v___x_5296_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5297_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5299_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5300_ = l_Lean_Parser_checkNoWsBefore(v___x_5299_);
return v___x_5300_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; 
v___x_5302_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5303_ = l_Lean_Parser_symbolNoAntiquot(v___x_5302_);
return v___x_5303_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5305_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5306_ = l_Lean_Parser_symbolNoAntiquot(v___x_5305_);
return v___x_5306_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5307_ = l_Lean_Parser_antiquotExpr;
v___x_5308_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5309_ = l_Lean_Parser_andthen(v___x_5308_, v___x_5307_);
return v___x_5309_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5310_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5311_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5312_ = l_Lean_Parser_andthen(v___x_5311_, v___x_5310_);
return v___x_5312_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5313_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5314_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5315_ = l_Lean_Parser_andthen(v___x_5314_, v___x_5313_);
return v___x_5315_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5317_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5318_ = l_Lean_Parser_andthen(v___x_5317_, v___x_5316_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5322_, lean_object* v_s_5323_){
_start:
{
lean_object* v_pos_5324_; lean_object* v_errorMsg_5325_; lean_object* v___x_5326_; uint8_t v___x_5327_; 
v_pos_5324_ = lean_ctor_get(v_s_5323_, 2);
v_errorMsg_5325_ = lean_ctor_get(v_s_5323_, 4);
v___x_5326_ = lean_box(0);
v___x_5327_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5325_, v___x_5326_);
if (v___x_5327_ == 0)
{
lean_dec_ref(v_c_5322_);
return v_s_5323_;
}
else
{
lean_object* v___x_5328_; lean_object* v_fn_5329_; lean_object* v_iniSz_5330_; lean_object* v_s_5331_; lean_object* v_errorMsg_5332_; uint8_t v___x_5333_; 
lean_inc(v_pos_5324_);
v___x_5328_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5329_ = lean_ctor_get(v___x_5328_, 1);
v_iniSz_5330_ = l_Lean_Parser_ParserState_stackSize(v_s_5323_);
lean_inc_ref(v_fn_5329_);
v_s_5331_ = lean_apply_2(v_fn_5329_, v_c_5322_, v_s_5323_);
v_errorMsg_5332_ = lean_ctor_get(v_s_5331_, 4);
lean_inc(v_errorMsg_5332_);
v___x_5333_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5332_, v___x_5326_);
lean_dec(v_errorMsg_5332_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; 
v___x_5334_ = l_Lean_Parser_ParserState_restore(v_s_5331_, v_iniSz_5330_, v_pos_5324_);
lean_dec(v_iniSz_5330_);
return v___x_5334_;
}
else
{
lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
lean_dec(v_pos_5324_);
v___x_5335_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5336_ = lean_unsigned_to_nat(1u);
v___x_5337_ = lean_nat_sub(v_iniSz_5330_, v___x_5336_);
lean_dec(v_iniSz_5330_);
v___x_5338_ = l_Lean_Parser_ParserState_mkNode(v_s_5331_, v___x_5335_, v___x_5337_);
lean_dec(v___x_5337_);
return v___x_5338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v_toInputContext_5342_; lean_object* v_s_5343_; lean_object* v_pos_5344_; lean_object* v_inputString_5345_; uint32_t v___x_5346_; uint32_t v___x_5347_; uint8_t v___x_5348_; 
v_toInputContext_5342_ = lean_ctor_get(v___y_5340_, 0);
lean_inc_ref(v___y_5340_);
v_s_5343_ = lean_apply_2(v_fn_5339_, v___y_5340_, v___y_5341_);
v_pos_5344_ = lean_ctor_get(v_s_5343_, 2);
lean_inc(v_pos_5344_);
v_inputString_5345_ = lean_ctor_get(v_toInputContext_5342_, 0);
v___x_5346_ = lean_string_utf8_get(v_inputString_5345_, v_pos_5344_);
lean_dec(v_pos_5344_);
v___x_5347_ = 37;
v___x_5348_ = lean_uint32_dec_eq(v___x_5346_, v___x_5347_);
if (v___x_5348_ == 0)
{
lean_dec_ref(v___y_5340_);
return v_s_5343_;
}
else
{
lean_object* v___x_5349_; 
v___x_5349_ = l_Lean_Parser_tokenAntiquotFn(v___y_5340_, v_s_5343_);
return v___x_5349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5350_){
_start:
{
lean_object* v_info_5351_; lean_object* v_fn_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5360_; 
v_info_5351_ = lean_ctor_get(v_p_5350_, 0);
v_fn_5352_ = lean_ctor_get(v_p_5350_, 1);
v_isSharedCheck_5360_ = !lean_is_exclusive(v_p_5350_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5354_ = v_p_5350_;
v_isShared_5355_ = v_isSharedCheck_5360_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_fn_5352_);
lean_inc(v_info_5351_);
lean_dec(v_p_5350_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5360_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___f_5356_; lean_object* v___x_5358_; 
v___f_5356_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5356_, 0, v_fn_5352_);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 1, v___f_5356_);
v___x_5358_ = v___x_5354_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_info_5351_);
lean_ctor_set(v_reuseFailAlloc_5359_, 1, v___f_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5361_){
_start:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; 
v___x_5362_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5361_);
v___x_5363_ = l_Lean_Parser_tokenWithAntiquot(v___x_5362_);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5366_, uint8_t v_includeIdent_5367_){
_start:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5366_, v_includeIdent_5367_);
v___x_5369_ = l_Lean_Parser_tokenWithAntiquot(v___x_5368_);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5370_, lean_object* v_includeIdent_5371_){
_start:
{
uint8_t v_includeIdent_boxed_5372_; lean_object* v_res_5373_; 
v_includeIdent_boxed_5372_ = lean_unbox(v_includeIdent_5371_);
v_res_5373_ = l_Lean_Parser_nonReservedSymbol(v_sym_5370_, v_includeIdent_boxed_5372_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5374_, lean_object* v_asciiSym_5375_){
_start:
{
lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5376_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5374_, v_asciiSym_5375_);
v___x_5377_ = l_Lean_Parser_tokenWithAntiquot(v___x_5376_);
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5378_, lean_object* v_asciiSym_5379_, uint8_t v_preserveForPP_5380_){
_start:
{
lean_object* v___x_5381_; 
v___x_5381_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5378_, v_asciiSym_5379_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5382_, lean_object* v_asciiSym_5383_, lean_object* v_preserveForPP_5384_){
_start:
{
uint8_t v_preserveForPP_boxed_5385_; lean_object* v_res_5386_; 
v_preserveForPP_boxed_5385_ = lean_unbox(v_preserveForPP_5384_);
v_res_5386_ = l_Lean_Parser_unicodeSymbol(v_sym_5382_, v_asciiSym_5383_, v_preserveForPP_boxed_5385_);
return v_res_5386_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5387_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5388_ = l_Lean_Parser_symbol(v___x_5387_);
return v___x_5388_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5389_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5390_ = lean_box(0);
v___x_5391_ = l_Lean_Parser_setExpected(v___x_5390_, v___x_5389_);
return v___x_5391_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5393_ = l_Lean_Parser_checkNoWsBefore(v___x_5392_);
return v___x_5393_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5394_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5395_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5396_ = l_Lean_Parser_andthen(v___x_5395_, v___x_5394_);
return v___x_5396_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5397_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5398_ = l_Lean_Parser_manyNoAntiquot(v___x_5397_);
return v___x_5398_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5400_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5401_ = l_Lean_Parser_checkNoWsBefore(v___x_5400_);
return v___x_5401_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5410_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5411_ = l_Lean_Parser_symbol(v___x_5410_);
return v___x_5411_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5412_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5413_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5414_ = l_Lean_Parser_andthen(v___x_5413_, v___x_5412_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5418_, lean_object* v_kind_5419_, uint8_t v_anonymous_5420_, uint8_t v_isPseudoKind_5421_){
_start:
{
lean_object* v___y_5423_; lean_object* v___y_5424_; lean_object* v___y_5437_; 
if (v_isPseudoKind_5421_ == 0)
{
lean_object* v___x_5455_; 
v___x_5455_ = lean_box(0);
v___y_5437_ = v___x_5455_;
goto v___jp_5436_;
}
else
{
lean_object* v___x_5456_; 
v___x_5456_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5437_ = v___x_5456_;
goto v___jp_5436_;
}
v___jp_5422_:
{
lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5425_ = l_Lean_Parser_maxPrec;
v___x_5426_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5427_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5428_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5429_ = l_Lean_Parser_antiquotExpr;
v___x_5430_ = l_Lean_Parser_andthen(v___x_5429_, v___y_5424_);
v___x_5431_ = l_Lean_Parser_andthen(v___x_5428_, v___x_5430_);
v___x_5432_ = l_Lean_Parser_andthen(v___x_5427_, v___x_5431_);
v___x_5433_ = l_Lean_Parser_andthen(v___x_5426_, v___x_5432_);
v___x_5434_ = l_Lean_Parser_atomic(v___x_5433_);
v___x_5435_ = l_Lean_Parser_leadingNode(v___y_5423_, v___x_5425_, v___x_5434_);
return v___x_5435_;
}
v___jp_5436_:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v_kind_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; uint8_t v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v_nameP_5452_; 
lean_inc(v___y_5437_);
v___x_5438_ = l_Lean_Name_append(v_kind_5419_, v___y_5437_);
v___x_5439_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5440_ = l_Lean_Name_append(v___x_5438_, v___x_5439_);
v___x_5441_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5442_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5443_ = lean_string_append(v___x_5442_, v_name_5418_);
v___x_5444_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5445_ = lean_string_append(v___x_5443_, v___x_5444_);
v___x_5446_ = l_Lean_Parser_checkNoWsBefore(v___x_5445_);
v___x_5447_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5448_ = 0;
v___x_5449_ = l_Lean_Parser_nonReservedSymbol(v_name_5418_, v___x_5448_);
v___x_5450_ = l_Lean_Parser_andthen(v___x_5447_, v___x_5449_);
v___x_5451_ = l_Lean_Parser_andthen(v___x_5446_, v___x_5450_);
v_nameP_5452_ = l_Lean_Parser_node(v___x_5441_, v___x_5451_);
if (v_anonymous_5420_ == 0)
{
v___y_5423_ = v_kind_5440_;
v___y_5424_ = v_nameP_5452_;
goto v___jp_5422_;
}
else
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5454_ = l_Lean_Parser_orelse(v_nameP_5452_, v___x_5453_);
v___y_5423_ = v_kind_5440_;
v___y_5424_ = v___x_5454_;
goto v___jp_5422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5457_, lean_object* v_kind_5458_, lean_object* v_anonymous_5459_, lean_object* v_isPseudoKind_5460_){
_start:
{
uint8_t v_anonymous_boxed_5461_; uint8_t v_isPseudoKind_boxed_5462_; lean_object* v_res_5463_; 
v_anonymous_boxed_5461_ = lean_unbox(v_anonymous_5459_);
v_isPseudoKind_boxed_5462_ = lean_unbox(v_isPseudoKind_5460_);
v_res_5463_ = l_Lean_Parser_mkAntiquot(v_name_5457_, v_kind_5458_, v_anonymous_boxed_5461_, v_isPseudoKind_boxed_5462_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; 
v___x_5471_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5472_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5473_ = l_Lean_addBuiltinDocString(v___x_5471_, v___x_5472_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5476_, lean_object* v_p_5477_, uint8_t v_isCatAntiquot_5478_, lean_object* v_c_5479_, lean_object* v_s_5480_){
_start:
{
lean_object* v_toInputContext_5481_; lean_object* v_pos_5482_; lean_object* v_inputString_5483_; uint32_t v___x_5484_; uint32_t v___x_5485_; uint8_t v___x_5486_; 
v_toInputContext_5481_ = lean_ctor_get(v_c_5479_, 0);
v_pos_5482_ = lean_ctor_get(v_s_5480_, 2);
v_inputString_5483_ = lean_ctor_get(v_toInputContext_5481_, 0);
v___x_5484_ = lean_string_utf8_get(v_inputString_5483_, v_pos_5482_);
v___x_5485_ = 36;
v___x_5486_ = lean_uint32_dec_eq(v___x_5484_, v___x_5485_);
if (v___x_5486_ == 0)
{
lean_object* v___x_5487_; 
lean_dec_ref(v_antiquotP_5476_);
v___x_5487_ = lean_apply_2(v_p_5477_, v_c_5479_, v_s_5480_);
return v___x_5487_;
}
else
{
if (v_isCatAntiquot_5478_ == 0)
{
uint8_t v___x_5488_; lean_object* v___x_5489_; 
v___x_5488_ = 1;
v___x_5489_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5476_, v_p_5477_, v___x_5488_, v_c_5479_, v_s_5480_);
return v___x_5489_;
}
else
{
uint8_t v___x_5490_; lean_object* v___x_5491_; 
v___x_5490_ = 0;
v___x_5491_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5476_, v_p_5477_, v___x_5490_, v_c_5479_, v_s_5480_);
return v___x_5491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5492_, lean_object* v_p_5493_, lean_object* v_isCatAntiquot_5494_, lean_object* v_c_5495_, lean_object* v_s_5496_){
_start:
{
uint8_t v_isCatAntiquot_boxed_5497_; lean_object* v_res_5498_; 
v_isCatAntiquot_boxed_5497_ = lean_unbox(v_isCatAntiquot_5494_);
v_res_5498_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5492_, v_p_5493_, v_isCatAntiquot_boxed_5497_, v_c_5495_, v_s_5496_);
return v_res_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5499_, lean_object* v_p_5500_){
_start:
{
lean_object* v_info_5501_; lean_object* v_fn_5502_; lean_object* v_info_5503_; lean_object* v_fn_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5515_; 
v_info_5501_ = lean_ctor_get(v_antiquotP_5499_, 0);
lean_inc_ref(v_info_5501_);
v_fn_5502_ = lean_ctor_get(v_antiquotP_5499_, 1);
lean_inc_ref(v_fn_5502_);
lean_dec_ref(v_antiquotP_5499_);
v_info_5503_ = lean_ctor_get(v_p_5500_, 0);
v_fn_5504_ = lean_ctor_get(v_p_5500_, 1);
v_isSharedCheck_5515_ = !lean_is_exclusive(v_p_5500_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5506_ = v_p_5500_;
v_isShared_5507_ = v_isSharedCheck_5515_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_fn_5504_);
lean_inc(v_info_5503_);
lean_dec(v_p_5500_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5515_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5508_; uint8_t v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5513_; 
v___x_5508_ = l_Lean_Parser_orelseInfo(v_info_5501_, v_info_5503_);
v___x_5509_ = 0;
v___x_5510_ = lean_box(v___x_5509_);
v___x_5511_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5511_, 0, v_fn_5502_);
lean_closure_set(v___x_5511_, 1, v_fn_5504_);
lean_closure_set(v___x_5511_, 2, v___x_5510_);
if (v_isShared_5507_ == 0)
{
lean_ctor_set(v___x_5506_, 1, v___x_5511_);
lean_ctor_set(v___x_5506_, 0, v___x_5508_);
v___x_5513_ = v___x_5506_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v___x_5511_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v___x_5523_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5524_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5525_ = l_Lean_addBuiltinDocString(v___x_5523_, v___x_5524_);
return v___x_5525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5528_){
_start:
{
lean_object* v_fn_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5537_; 
v_fn_5529_ = lean_ctor_get(v_p_5528_, 1);
v_isSharedCheck_5537_ = !lean_is_exclusive(v_p_5528_);
if (v_isSharedCheck_5537_ == 0)
{
lean_object* v_unused_5538_; 
v_unused_5538_ = lean_ctor_get(v_p_5528_, 0);
lean_dec(v_unused_5538_);
v___x_5531_ = v_p_5528_;
v_isShared_5532_ = v_isSharedCheck_5537_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_fn_5529_);
lean_dec(v_p_5528_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5537_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v___x_5533_; lean_object* v___x_5535_; 
v___x_5533_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5532_ == 0)
{
lean_ctor_set(v___x_5531_, 0, v___x_5533_);
v___x_5535_ = v___x_5531_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v___x_5533_);
lean_ctor_set(v_reuseFailAlloc_5536_, 1, v_fn_5529_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5542_; lean_object* v___x_5543_; 
v___x_5542_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5543_ = l_Lean_Parser_symbol(v___x_5542_);
return v___x_5543_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5544_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5545_ = l_Lean_Parser_symbol(v___x_5544_);
return v___x_5545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5546_, lean_object* v_p_5547_, lean_object* v_suffix_5548_){
_start:
{
lean_object* v___x_5549_; lean_object* v_kind_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5549_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5550_ = l_Lean_Name_append(v_kind_5546_, v___x_5549_);
v___x_5551_ = l_Lean_Parser_maxPrec;
v___x_5552_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5553_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5554_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5555_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5556_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5557_ = l_Lean_Parser_node(v___x_5556_, v_p_5547_);
v___x_5558_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5559_ = l_Lean_Parser_andthen(v___x_5558_, v_suffix_5548_);
v___x_5560_ = l_Lean_Parser_andthen(v___x_5557_, v___x_5559_);
v___x_5561_ = l_Lean_Parser_andthen(v___x_5555_, v___x_5560_);
v___x_5562_ = l_Lean_Parser_andthen(v___x_5554_, v___x_5561_);
v___x_5563_ = l_Lean_Parser_andthen(v___x_5553_, v___x_5562_);
v___x_5564_ = l_Lean_Parser_andthen(v___x_5552_, v___x_5563_);
v___x_5565_ = l_Lean_Parser_atomic(v___x_5564_);
v___x_5566_ = l_Lean_Parser_leadingNode(v_kind_5550_, v___x_5551_, v___x_5565_);
return v___x_5566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5574_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5575_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5576_ = l_Lean_addBuiltinDocString(v___x_5574_, v___x_5575_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5577_){
_start:
{
lean_object* v_res_5578_; 
v_res_5578_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5582_, lean_object* v_suffix_5583_, lean_object* v_c_5584_, lean_object* v_s_5585_){
_start:
{
lean_object* v_pos_5586_; lean_object* v_iniSz_5587_; lean_object* v_s_5588_; lean_object* v_stxStack_5589_; lean_object* v_errorMsg_5590_; lean_object* v___x_5591_; uint8_t v___x_5592_; 
v_pos_5586_ = lean_ctor_get(v_s_5585_, 2);
lean_inc(v_pos_5586_);
v_iniSz_5587_ = l_Lean_Parser_ParserState_stackSize(v_s_5585_);
v_s_5588_ = lean_apply_2(v_suffix_5583_, v_c_5584_, v_s_5585_);
v_stxStack_5589_ = lean_ctor_get(v_s_5588_, 0);
lean_inc_ref(v_stxStack_5589_);
v_errorMsg_5590_ = lean_ctor_get(v_s_5588_, 4);
lean_inc(v_errorMsg_5590_);
v___x_5591_ = lean_box(0);
v___x_5592_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5590_, v___x_5591_);
lean_dec(v_errorMsg_5590_);
if (v___x_5592_ == 0)
{
lean_object* v___x_5593_; 
lean_dec_ref(v_stxStack_5589_);
lean_dec(v_kind_5582_);
v___x_5593_ = l_Lean_Parser_ParserState_restore(v_s_5588_, v_iniSz_5587_, v_pos_5586_);
lean_dec(v_iniSz_5587_);
return v___x_5593_;
}
else
{
lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
lean_dec(v_iniSz_5587_);
lean_dec(v_pos_5586_);
v___x_5594_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5595_ = l_Lean_Name_append(v_kind_5582_, v___x_5594_);
v___x_5596_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5589_);
lean_dec_ref(v_stxStack_5589_);
v___x_5597_ = lean_unsigned_to_nat(2u);
v___x_5598_ = lean_nat_sub(v___x_5596_, v___x_5597_);
lean_dec(v___x_5596_);
v___x_5599_ = l_Lean_Parser_ParserState_mkNode(v_s_5588_, v___x_5595_, v___x_5598_);
lean_dec(v___x_5598_);
return v___x_5599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5600_, lean_object* v_kind_5601_, lean_object* v_fn_5602_, lean_object* v_c_5603_, lean_object* v_s_5604_){
_start:
{
lean_object* v_s_5605_; lean_object* v_stxStack_5606_; lean_object* v_errorMsg_5607_; lean_object* v___x_5608_; uint8_t v___x_5609_; 
lean_inc_ref(v_c_5603_);
v_s_5605_ = lean_apply_2(v_fn_5600_, v_c_5603_, v_s_5604_);
v_stxStack_5606_ = lean_ctor_get(v_s_5605_, 0);
lean_inc_ref(v_stxStack_5606_);
v_errorMsg_5607_ = lean_ctor_get(v_s_5605_, 4);
lean_inc(v_errorMsg_5607_);
v___x_5608_ = lean_box(0);
v___x_5609_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5607_, v___x_5608_);
lean_dec(v_errorMsg_5607_);
if (v___x_5609_ == 0)
{
lean_dec_ref(v_stxStack_5606_);
lean_dec_ref(v_c_5603_);
lean_dec_ref(v_fn_5602_);
lean_dec(v_kind_5601_);
return v_s_5605_;
}
else
{
lean_object* v___x_5610_; uint8_t v___x_5611_; 
v___x_5610_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5606_);
lean_dec_ref(v_stxStack_5606_);
v___x_5611_ = l_Lean_Syntax_isAntiquots(v___x_5610_);
if (v___x_5611_ == 0)
{
lean_dec_ref(v_c_5603_);
lean_dec_ref(v_fn_5602_);
lean_dec(v_kind_5601_);
return v_s_5605_;
}
else
{
lean_object* v___x_5612_; 
v___x_5612_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5601_, v_fn_5602_, v_c_5603_, v_s_5605_);
return v___x_5612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5613_, lean_object* v_p_5614_, lean_object* v_suffix_5615_){
_start:
{
lean_object* v_info_5616_; lean_object* v_fn_5617_; lean_object* v_info_5618_; lean_object* v_fn_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5628_; 
v_info_5616_ = lean_ctor_get(v_p_5614_, 0);
lean_inc_ref(v_info_5616_);
v_fn_5617_ = lean_ctor_get(v_p_5614_, 1);
lean_inc_ref(v_fn_5617_);
lean_dec_ref(v_p_5614_);
v_info_5618_ = lean_ctor_get(v_suffix_5615_, 0);
v_fn_5619_ = lean_ctor_get(v_suffix_5615_, 1);
v_isSharedCheck_5628_ = !lean_is_exclusive(v_suffix_5615_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5621_ = v_suffix_5615_;
v_isShared_5622_ = v_isSharedCheck_5628_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_fn_5619_);
lean_inc(v_info_5618_);
lean_dec(v_suffix_5615_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5628_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___f_5623_; lean_object* v___x_5624_; lean_object* v___x_5626_; 
v___f_5623_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5623_, 0, v_fn_5617_);
lean_closure_set(v___f_5623_, 1, v_kind_5613_);
lean_closure_set(v___f_5623_, 2, v_fn_5619_);
v___x_5624_ = l_Lean_Parser_andthenInfo(v_info_5616_, v_info_5618_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 1, v___f_5623_);
lean_ctor_set(v___x_5621_, 0, v___x_5624_);
v___x_5626_ = v___x_5621_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5627_, 1, v___f_5623_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; 
v___x_5636_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5637_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5638_ = l_Lean_addBuiltinDocString(v___x_5636_, v___x_5637_);
return v___x_5638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5641_, lean_object* v_p_5642_, lean_object* v_suffix_5643_){
_start:
{
lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; 
lean_inc_ref(v_p_5642_);
v___x_5644_ = l_Lean_Parser_withoutInfo(v_p_5642_);
lean_inc_ref(v_suffix_5643_);
lean_inc(v_kind_5641_);
v___x_5645_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5641_, v___x_5644_, v_suffix_5643_);
v___x_5646_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5641_, v_p_5642_, v_suffix_5643_);
v___x_5647_ = l_Lean_Parser_withAntiquot(v___x_5645_, v___x_5646_);
return v___x_5647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5648_, lean_object* v_kind_5649_, lean_object* v_p_5650_, uint8_t v_anonymous_5651_){
_start:
{
uint8_t v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
v___x_5652_ = 0;
lean_inc(v_kind_5649_);
v___x_5653_ = l_Lean_Parser_mkAntiquot(v_name_5648_, v_kind_5649_, v_anonymous_5651_, v___x_5652_);
v___x_5654_ = l_Lean_Parser_node(v_kind_5649_, v_p_5650_);
v___x_5655_ = l_Lean_Parser_withAntiquot(v___x_5653_, v___x_5654_);
return v___x_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5656_, lean_object* v_kind_5657_, lean_object* v_p_5658_, lean_object* v_anonymous_5659_){
_start:
{
uint8_t v_anonymous_boxed_5660_; lean_object* v_res_5661_; 
v_anonymous_boxed_5660_ = lean_unbox(v_anonymous_5659_);
v_res_5661_ = l_Lean_Parser_nodeWithAntiquot(v_name_5656_, v_kind_5657_, v_p_5658_, v_anonymous_boxed_5660_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5666_, lean_object* v_sep_5667_){
_start:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v_str_5672_; lean_object* v_startInclusive_5673_; lean_object* v_endExclusive_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5668_ = lean_unsigned_to_nat(0u);
v___x_5669_ = lean_string_utf8_byte_size(v_sep_5667_);
v___x_5670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5670_, 0, v_sep_5667_);
lean_ctor_set(v___x_5670_, 1, v___x_5668_);
lean_ctor_set(v___x_5670_, 2, v___x_5669_);
v___x_5671_ = l_String_Slice_trimAscii(v___x_5670_);
v_str_5672_ = lean_ctor_get(v___x_5671_, 0);
lean_inc_ref(v_str_5672_);
v_startInclusive_5673_ = lean_ctor_get(v___x_5671_, 1);
lean_inc(v_startInclusive_5673_);
v_endExclusive_5674_ = lean_ctor_get(v___x_5671_, 2);
lean_inc(v_endExclusive_5674_);
lean_dec_ref(v___x_5671_);
v___x_5675_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5676_ = lean_string_utf8_extract_fast(v_str_5672_, v_startInclusive_5673_, v_endExclusive_5674_);
lean_dec(v_endExclusive_5674_);
lean_dec(v_startInclusive_5673_);
lean_dec_ref(v_str_5672_);
v___x_5677_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5678_ = lean_string_append(v___x_5676_, v___x_5677_);
v___x_5679_ = l_Lean_Parser_symbol(v___x_5678_);
v___x_5680_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5675_, v_p_5666_, v___x_5679_);
return v___x_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5681_, lean_object* v_sep_5682_, lean_object* v_psep_5683_, uint8_t v_allowTrailingSep_5684_){
_start:
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
v___x_5685_ = l_Lean_Parser_sepByElemParser(v_p_5681_, v_sep_5682_);
v___x_5686_ = l_Lean_Parser_sepByNoAntiquot(v___x_5685_, v_psep_5683_, v_allowTrailingSep_5684_);
return v___x_5686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5687_, lean_object* v_sep_5688_, lean_object* v_psep_5689_, lean_object* v_allowTrailingSep_5690_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5691_; lean_object* v_res_5692_; 
v_allowTrailingSep_boxed_5691_ = lean_unbox(v_allowTrailingSep_5690_);
v_res_5692_ = l_Lean_Parser_sepBy(v_p_5687_, v_sep_5688_, v_psep_5689_, v_allowTrailingSep_boxed_5691_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5693_, lean_object* v_sep_5694_, lean_object* v_psep_5695_, uint8_t v_allowTrailingSep_5696_){
_start:
{
lean_object* v___x_5697_; lean_object* v___x_5698_; 
v___x_5697_ = l_Lean_Parser_sepByElemParser(v_p_5693_, v_sep_5694_);
v___x_5698_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5697_, v_psep_5695_, v_allowTrailingSep_5696_);
return v___x_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5699_, lean_object* v_sep_5700_, lean_object* v_psep_5701_, lean_object* v_allowTrailingSep_5702_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5703_; lean_object* v_res_5704_; 
v_allowTrailingSep_boxed_5703_ = lean_unbox(v_allowTrailingSep_5702_);
v_res_5704_ = l_Lean_Parser_sepBy1(v_p_5699_, v_sep_5700_, v_psep_5701_, v_allowTrailingSep_boxed_5703_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5705_, lean_object* v_iniSz_5706_){
_start:
{
lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v___x_5707_ = l_Lean_Parser_ParserState_stackSize(v_s_5705_);
v___x_5708_ = lean_unsigned_to_nat(1u);
v___x_5709_ = lean_nat_add(v_iniSz_5706_, v___x_5708_);
v___x_5710_ = lean_nat_dec_eq(v___x_5707_, v___x_5709_);
lean_dec(v___x_5709_);
lean_dec(v___x_5707_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; lean_object* v___x_5712_; 
v___x_5711_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5712_ = l_Lean_Parser_ParserState_mkNode(v_s_5705_, v___x_5711_, v_iniSz_5706_);
return v___x_5712_;
}
else
{
return v_s_5705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5713_, lean_object* v_iniSz_5714_){
_start:
{
lean_object* v_res_5715_; 
v_res_5715_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5713_, v_iniSz_5714_);
lean_dec(v_iniSz_5714_);
return v_res_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5716_, lean_object* v_tables_5717_, uint8_t v_behavior_5718_, lean_object* v_c_5719_, lean_object* v_s_5720_){
_start:
{
lean_object* v_leadingTable_5721_; lean_object* v_leadingParsers_5722_; lean_object* v_iniSz_5723_; lean_object* v___x_5724_; lean_object* v_fst_5725_; lean_object* v_snd_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5748_; 
v_leadingTable_5721_ = lean_ctor_get(v_tables_5717_, 0);
lean_inc(v_leadingTable_5721_);
v_leadingParsers_5722_ = lean_ctor_get(v_tables_5717_, 1);
lean_inc(v_leadingParsers_5722_);
lean_dec_ref(v_tables_5717_);
v_iniSz_5723_ = l_Lean_Parser_ParserState_stackSize(v_s_5720_);
lean_inc_ref(v_c_5719_);
v___x_5724_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5721_, v_c_5719_, v_s_5720_, v_behavior_5718_);
lean_dec(v_leadingTable_5721_);
v_fst_5725_ = lean_ctor_get(v___x_5724_, 0);
v_snd_5726_ = lean_ctor_get(v___x_5724_, 1);
v_isSharedCheck_5748_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5728_ = v___x_5724_;
v_isShared_5729_ = v_isSharedCheck_5748_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_snd_5726_);
lean_inc(v_fst_5725_);
lean_dec(v___x_5724_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5748_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v_errorMsg_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v_errorMsg_5730_ = lean_ctor_get(v_fst_5725_, 4);
v___x_5731_ = lean_box(0);
v___x_5732_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5730_, v___x_5731_);
if (v___x_5732_ == 0)
{
lean_del_object(v___x_5728_);
lean_dec(v_snd_5726_);
lean_dec(v_iniSz_5723_);
lean_dec(v_leadingParsers_5722_);
lean_dec_ref(v_c_5719_);
lean_dec(v_kind_5716_);
return v_fst_5725_;
}
else
{
lean_object* v_ps_5733_; uint8_t v___x_5734_; 
v_ps_5733_ = l_List_appendTR___redArg(v_leadingParsers_5722_, v_snd_5726_);
v___x_5734_ = l_List_isEmpty___redArg(v_ps_5733_);
if (v___x_5734_ == 0)
{
lean_object* v_s_5735_; lean_object* v___x_5736_; 
lean_del_object(v___x_5728_);
lean_dec(v_kind_5716_);
v_s_5735_ = l_Lean_Parser_longestMatchFn(v___x_5731_, v_ps_5733_, v_c_5719_, v_fst_5725_);
v___x_5736_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5735_, v_iniSz_5723_);
lean_dec(v_iniSz_5723_);
return v___x_5736_;
}
else
{
lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5740_; 
lean_dec(v_ps_5733_);
lean_dec(v_iniSz_5723_);
v___x_5737_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5716_, v___x_5734_);
v___x_5738_ = lean_box(0);
lean_inc_ref(v___x_5737_);
if (v_isShared_5729_ == 0)
{
lean_ctor_set_tag(v___x_5728_, 1);
lean_ctor_set(v___x_5728_, 1, v___x_5738_);
lean_ctor_set(v___x_5728_, 0, v___x_5737_);
v___x_5740_ = v___x_5728_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5737_);
lean_ctor_set(v_reuseFailAlloc_5747_, 1, v___x_5738_);
v___x_5740_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
lean_object* v_s_5741_; lean_object* v_errorMsg_5745_; uint8_t v___x_5746_; 
v_s_5741_ = l_Lean_Parser_tokenFn(v___x_5740_, v_c_5719_, v_fst_5725_);
v_errorMsg_5745_ = lean_ctor_get(v_s_5741_, 4);
lean_inc(v_errorMsg_5745_);
v___x_5746_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5745_, v___x_5731_);
lean_dec(v_errorMsg_5745_);
if (v___x_5746_ == 0)
{
if (v___x_5734_ == 0)
{
goto v___jp_5742_;
}
else
{
lean_dec_ref(v___x_5737_);
return v_s_5741_;
}
}
else
{
goto v___jp_5742_;
}
v___jp_5742_:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; 
v___x_5743_ = lean_unsigned_to_nat(0u);
v___x_5744_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5741_, v___x_5737_, v___x_5743_);
return v___x_5744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5749_, lean_object* v_tables_5750_, lean_object* v_behavior_5751_, lean_object* v_c_5752_, lean_object* v_s_5753_){
_start:
{
uint8_t v_behavior_boxed_5754_; lean_object* v_res_5755_; 
v_behavior_boxed_5754_ = lean_unbox(v_behavior_5751_);
v_res_5755_ = l_Lean_Parser_leadingParserAux(v_kind_5749_, v_tables_5750_, v_behavior_boxed_5754_, v_c_5752_, v_s_5753_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5756_, lean_object* v_tables_5757_, uint8_t v_behavior_5758_, lean_object* v_antiquotParser_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_){
_start:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; uint8_t v___x_5764_; lean_object* v___x_5765_; 
v___x_5762_ = lean_box(v_behavior_5758_);
v___x_5763_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5763_, 0, v_kind_5756_);
lean_closure_set(v___x_5763_, 1, v_tables_5757_);
lean_closure_set(v___x_5763_, 2, v___x_5762_);
v___x_5764_ = 1;
v___x_5765_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5759_, v___x_5763_, v___x_5764_, v_a_5760_, v_a_5761_);
return v___x_5765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5766_, lean_object* v_tables_5767_, lean_object* v_behavior_5768_, lean_object* v_antiquotParser_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_){
_start:
{
uint8_t v_behavior_boxed_5772_; lean_object* v_res_5773_; 
v_behavior_boxed_5772_ = lean_unbox(v_behavior_5768_);
v_res_5773_ = l_Lean_Parser_leadingParser(v_kind_5766_, v_tables_5767_, v_behavior_boxed_5772_, v_antiquotParser_5769_, v_a_5770_, v_a_5771_);
return v_res_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5774_, lean_object* v_left_5775_, lean_object* v_ps_5776_, lean_object* v_c_5777_, lean_object* v_s_5778_){
_start:
{
lean_object* v_trailingParsers_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; 
v_trailingParsers_5779_ = lean_ctor_get(v_tables_5774_, 3);
lean_inc(v_trailingParsers_5779_);
lean_dec_ref(v_tables_5774_);
v___x_5780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5780_, 0, v_left_5775_);
v___x_5781_ = l_List_appendTR___redArg(v_ps_5776_, v_trailingParsers_5779_);
v___x_5782_ = l_Lean_Parser_longestMatchFn(v___x_5780_, v___x_5781_, v_c_5777_, v_s_5778_);
return v___x_5782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5783_, lean_object* v_c_5784_, lean_object* v_s_5785_){
_start:
{
lean_object* v_pos_5786_; lean_object* v_trailingTable_5787_; lean_object* v_trailingParsers_5788_; lean_object* v_iniSz_5789_; uint8_t v___x_5790_; lean_object* v___x_5791_; lean_object* v_fst_5792_; lean_object* v_snd_5793_; lean_object* v_stxStack_5794_; lean_object* v_errorMsg_5795_; lean_object* v___x_5810_; uint8_t v___x_5811_; 
v_pos_5786_ = lean_ctor_get(v_s_5785_, 2);
lean_inc(v_pos_5786_);
v_trailingTable_5787_ = lean_ctor_get(v_tables_5783_, 2);
v_trailingParsers_5788_ = lean_ctor_get(v_tables_5783_, 3);
v_iniSz_5789_ = l_Lean_Parser_ParserState_stackSize(v_s_5785_);
v___x_5790_ = 0;
lean_inc_ref(v_c_5784_);
v___x_5791_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5787_, v_c_5784_, v_s_5785_, v___x_5790_);
v_fst_5792_ = lean_ctor_get(v___x_5791_, 0);
lean_inc(v_fst_5792_);
v_snd_5793_ = lean_ctor_get(v___x_5791_, 1);
lean_inc(v_snd_5793_);
lean_dec_ref(v___x_5791_);
v_stxStack_5794_ = lean_ctor_get(v_fst_5792_, 0);
v_errorMsg_5795_ = lean_ctor_get(v_fst_5792_, 4);
v___x_5810_ = lean_box(0);
v___x_5811_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5795_, v___x_5810_);
if (v___x_5811_ == 0)
{
lean_object* v___x_5812_; 
lean_dec(v_snd_5793_);
lean_dec_ref(v_c_5784_);
lean_dec_ref(v_tables_5783_);
v___x_5812_ = l_Lean_Parser_ParserState_restore(v_fst_5792_, v_iniSz_5789_, v_pos_5786_);
lean_dec(v_iniSz_5789_);
return v___x_5812_;
}
else
{
uint8_t v___x_5813_; 
v___x_5813_ = l_List_isEmpty___redArg(v_snd_5793_);
if (v___x_5813_ == 0)
{
goto v___jp_5796_;
}
else
{
uint8_t v___x_5814_; 
v___x_5814_ = l_List_isEmpty___redArg(v_trailingParsers_5788_);
if (v___x_5814_ == 0)
{
goto v___jp_5796_;
}
else
{
lean_dec(v_snd_5793_);
lean_dec(v_iniSz_5789_);
lean_dec(v_pos_5786_);
lean_dec_ref(v_c_5784_);
lean_dec_ref(v_tables_5783_);
return v_fst_5792_;
}
}
}
v___jp_5796_:
{
lean_object* v_left_5797_; lean_object* v_s_5798_; lean_object* v_s_5799_; lean_object* v_pos_5800_; lean_object* v_errorMsg_5801_; lean_object* v___x_5802_; uint8_t v___x_5803_; 
v_left_5797_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5794_);
v_s_5798_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5792_);
lean_inc_ref(v_c_5784_);
lean_inc(v_left_5797_);
lean_inc_ref(v_tables_5783_);
v_s_5799_ = l_Lean_Parser_trailingLoopStep(v_tables_5783_, v_left_5797_, v_snd_5793_, v_c_5784_, v_s_5798_);
v_pos_5800_ = lean_ctor_get(v_s_5799_, 2);
lean_inc(v_pos_5800_);
v_errorMsg_5801_ = lean_ctor_get(v_s_5799_, 4);
lean_inc(v_errorMsg_5801_);
v___x_5802_ = lean_box(0);
v___x_5803_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5801_, v___x_5802_);
lean_dec(v_errorMsg_5801_);
if (v___x_5803_ == 0)
{
uint8_t v_decide_5804_; 
lean_dec_ref(v_c_5784_);
lean_dec_ref(v_tables_5783_);
v_decide_5804_ = lean_nat_dec_eq(v_pos_5800_, v_pos_5786_);
lean_dec(v_pos_5800_);
if (v_decide_5804_ == 0)
{
lean_dec(v_left_5797_);
lean_dec(v_iniSz_5789_);
lean_dec(v_pos_5786_);
return v_s_5799_;
}
else
{
lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5805_ = lean_unsigned_to_nat(1u);
v___x_5806_ = lean_nat_sub(v_iniSz_5789_, v___x_5805_);
lean_dec(v_iniSz_5789_);
v___x_5807_ = l_Lean_Parser_ParserState_restore(v_s_5799_, v___x_5806_, v_pos_5786_);
lean_dec(v___x_5806_);
v___x_5808_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5807_, v_left_5797_);
return v___x_5808_;
}
}
else
{
lean_dec(v_pos_5800_);
lean_dec(v_left_5797_);
lean_dec(v_iniSz_5789_);
lean_dec(v_pos_5786_);
v_s_5785_ = v_s_5799_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5815_, lean_object* v_tables_5816_, uint8_t v_behavior_5817_, lean_object* v_antiquotParser_5818_, lean_object* v_c_5819_, lean_object* v_s_5820_){
_start:
{
lean_object* v_s_5821_; lean_object* v_errorMsg_5822_; lean_object* v___x_5823_; uint8_t v___x_5824_; 
lean_inc_ref(v_c_5819_);
lean_inc_ref(v_tables_5816_);
v_s_5821_ = l_Lean_Parser_leadingParser(v_kind_5815_, v_tables_5816_, v_behavior_5817_, v_antiquotParser_5818_, v_c_5819_, v_s_5820_);
v_errorMsg_5822_ = lean_ctor_get(v_s_5821_, 4);
lean_inc(v_errorMsg_5822_);
v___x_5823_ = lean_box(0);
v___x_5824_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5822_, v___x_5823_);
lean_dec(v_errorMsg_5822_);
if (v___x_5824_ == 0)
{
lean_dec_ref(v_c_5819_);
lean_dec_ref(v_tables_5816_);
return v_s_5821_;
}
else
{
lean_object* v___x_5825_; 
v___x_5825_ = l_Lean_Parser_trailingLoop(v_tables_5816_, v_c_5819_, v_s_5821_);
return v___x_5825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5826_, lean_object* v_tables_5827_, lean_object* v_behavior_5828_, lean_object* v_antiquotParser_5829_, lean_object* v_c_5830_, lean_object* v_s_5831_){
_start:
{
uint8_t v_behavior_boxed_5832_; lean_object* v_res_5833_; 
v_behavior_boxed_5832_ = lean_unbox(v_behavior_5828_);
v_res_5833_ = l_Lean_Parser_prattParser(v_kind_5826_, v_tables_5827_, v_behavior_boxed_5832_, v_antiquotParser_5829_, v_c_5830_, v_s_5831_);
return v_res_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5838_, lean_object* v_s_5839_){
_start:
{
lean_object* v_toInputContext_5840_; lean_object* v_pos_5841_; lean_object* v_inputString_5842_; lean_object* v_initStackSz_5843_; uint32_t v_curr_5848_; uint32_t v___x_5849_; uint8_t v___x_5850_; 
v_toInputContext_5840_ = lean_ctor_get(v_c_5838_, 0);
v_pos_5841_ = lean_ctor_get(v_s_5839_, 2);
lean_inc(v_pos_5841_);
v_inputString_5842_ = lean_ctor_get(v_toInputContext_5840_, 0);
v_initStackSz_5843_ = l_Lean_Parser_ParserState_stackSize(v_s_5839_);
v_curr_5848_ = lean_string_utf8_get(v_inputString_5842_, v_pos_5841_);
v___x_5849_ = 48;
v___x_5850_ = lean_uint32_dec_le(v___x_5849_, v_curr_5848_);
if (v___x_5850_ == 0)
{
lean_dec_ref(v_c_5838_);
goto v___jp_5844_;
}
else
{
uint32_t v___x_5851_; uint8_t v___x_5852_; 
v___x_5851_ = 57;
v___x_5852_ = lean_uint32_dec_le(v_curr_5848_, v___x_5851_);
if (v___x_5852_ == 0)
{
lean_dec_ref(v_c_5838_);
goto v___jp_5844_;
}
else
{
uint8_t v___x_5853_; 
v___x_5853_ = lean_uint32_dec_eq(v_curr_5848_, v___x_5849_);
if (v___x_5853_ == 0)
{
lean_object* v___f_5854_; lean_object* v_s_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; 
lean_dec(v_initStackSz_5843_);
v___f_5854_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_s_5855_ = l_Lean_Parser_takeWhileFn(v___f_5854_, v_c_5838_, v_s_5839_);
v___x_5856_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5857_ = l_Lean_Parser_mkNodeToken(v___x_5856_, v_pos_5841_, v___x_5852_, v_c_5838_, v_s_5855_);
return v___x_5857_;
}
else
{
lean_dec_ref(v_c_5838_);
goto v___jp_5844_;
}
}
}
v___jp_5844_:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5845_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5846_, 0, v_initStackSz_5843_);
v___x_5847_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5839_, v___x_5845_, v_pos_5841_, v___x_5846_);
lean_dec_ref_known(v___x_5846_, 1);
return v___x_5847_;
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5858_; uint8_t v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5858_ = 0;
v___x_5859_ = 1;
v___x_5860_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5861_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5862_ = l_Lean_Parser_mkAntiquot(v___x_5861_, v___x_5860_, v___x_5859_, v___x_5858_);
return v___x_5862_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5863_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5864_ = l_Lean_Parser_mkAtomicInfo(v___x_5863_);
return v___x_5864_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5865_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5866_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5867_, 0, v___x_5866_);
lean_ctor_set(v___x_5867_, 1, v___x_5865_);
return v___x_5867_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5868_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5869_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5870_ = l_Lean_Parser_withAntiquot(v___x_5869_, v___x_5868_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5871_; 
v___x_5871_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5872_, lean_object* v_s_5873_){
_start:
{
lean_inc_ref(v_s_5873_);
return v_s_5873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5874_, lean_object* v_s_5875_){
_start:
{
lean_object* v_res_5876_; 
v_res_5876_ = l_Lean_Parser_skip___lam__0(v_x_5874_, v_s_5875_);
lean_dec_ref(v_s_5875_);
lean_dec_ref(v_x_5874_);
return v_res_5876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5882_, lean_object* v_s_5883_, lean_object* v_f_5884_, lean_object* v_b_5885_){
_start:
{
lean_object* v_toApplicative_5886_; lean_object* v_toPure_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; uint8_t v___x_5891_; 
v_toApplicative_5886_ = lean_ctor_get(v_inst_5882_, 0);
v_toPure_5887_ = lean_ctor_get(v_toApplicative_5886_, 1);
v___x_5888_ = l_Lean_Syntax_getArgs(v_s_5883_);
v___x_5889_ = lean_unsigned_to_nat(0u);
v___x_5890_ = lean_array_get_size(v___x_5888_);
v___x_5891_ = lean_nat_dec_lt(v___x_5889_, v___x_5890_);
if (v___x_5891_ == 0)
{
lean_object* v___x_5892_; 
lean_inc(v_toPure_5887_);
lean_dec_ref(v___x_5888_);
lean_dec(v_f_5884_);
lean_dec_ref(v_inst_5882_);
v___x_5892_ = lean_apply_2(v_toPure_5887_, lean_box(0), v_b_5885_);
return v___x_5892_;
}
else
{
lean_object* v___x_5893_; uint8_t v___x_5894_; 
v___x_5893_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5893_, 0, lean_box(0));
lean_closure_set(v___x_5893_, 1, lean_box(0));
lean_closure_set(v___x_5893_, 2, lean_box(0));
lean_closure_set(v___x_5893_, 3, v_f_5884_);
v___x_5894_ = lean_nat_dec_le(v___x_5890_, v___x_5890_);
if (v___x_5894_ == 0)
{
if (v___x_5891_ == 0)
{
lean_object* v___x_5895_; 
lean_inc(v_toPure_5887_);
lean_dec_ref(v___x_5893_);
lean_dec_ref(v___x_5888_);
lean_dec_ref(v_inst_5882_);
v___x_5895_ = lean_apply_2(v_toPure_5887_, lean_box(0), v_b_5885_);
return v___x_5895_;
}
else
{
size_t v___x_5896_; size_t v___x_5897_; lean_object* v___x_5898_; 
v___x_5896_ = ((size_t)0ULL);
v___x_5897_ = lean_usize_of_nat(v___x_5890_);
v___x_5898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5882_, v___x_5893_, v___x_5888_, v___x_5896_, v___x_5897_, v_b_5885_);
return v___x_5898_;
}
}
else
{
size_t v___x_5899_; size_t v___x_5900_; lean_object* v___x_5901_; 
v___x_5899_ = ((size_t)0ULL);
v___x_5900_ = lean_usize_of_nat(v___x_5890_);
v___x_5901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5882_, v___x_5893_, v___x_5888_, v___x_5899_, v___x_5900_, v_b_5885_);
return v___x_5901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5902_, lean_object* v_s_5903_, lean_object* v_f_5904_, lean_object* v_b_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5902_, v_s_5903_, v_f_5904_, v_b_5905_);
lean_dec(v_s_5903_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5907_, lean_object* v_inst_5908_, lean_object* v_00_u03b2_5909_, lean_object* v_s_5910_, lean_object* v_f_5911_, lean_object* v_b_5912_){
_start:
{
lean_object* v___x_5913_; 
v___x_5913_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5908_, v_s_5910_, v_f_5911_, v_b_5912_);
return v___x_5913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5914_, lean_object* v_inst_5915_, lean_object* v_00_u03b2_5916_, lean_object* v_s_5917_, lean_object* v_f_5918_, lean_object* v_b_5919_){
_start:
{
lean_object* v_res_5920_; 
v_res_5920_ = l_Lean_Syntax_foldArgsM(v_m_5914_, v_inst_5915_, v_00_u03b2_5916_, v_s_5917_, v_f_5918_, v_b_5919_);
lean_dec(v_s_5917_);
return v_res_5920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5921_, lean_object* v_x1_5922_, lean_object* v_x2_5923_){
_start:
{
lean_object* v___x_5924_; 
v___x_5924_ = lean_apply_2(v_f_5921_, v_x1_5922_, v_x2_5923_);
return v___x_5924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5925_, lean_object* v_as_5926_, size_t v_i_5927_, size_t v_stop_5928_, lean_object* v_b_5929_){
_start:
{
uint8_t v___x_5930_; 
v___x_5930_ = lean_usize_dec_eq(v_i_5927_, v_stop_5928_);
if (v___x_5930_ == 0)
{
lean_object* v___x_5931_; lean_object* v___x_5932_; size_t v___x_5933_; size_t v___x_5934_; 
v___x_5931_ = lean_array_uget_borrowed(v_as_5926_, v_i_5927_);
lean_inc(v_f_5925_);
lean_inc(v___x_5931_);
v___x_5932_ = lean_apply_2(v_f_5925_, v___x_5931_, v_b_5929_);
v___x_5933_ = ((size_t)1ULL);
v___x_5934_ = lean_usize_add(v_i_5927_, v___x_5933_);
v_i_5927_ = v___x_5934_;
v_b_5929_ = v___x_5932_;
goto _start;
}
else
{
lean_dec(v_f_5925_);
return v_b_5929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5936_, lean_object* v_as_5937_, lean_object* v_i_5938_, lean_object* v_stop_5939_, lean_object* v_b_5940_){
_start:
{
size_t v_i_boxed_5941_; size_t v_stop_boxed_5942_; lean_object* v_res_5943_; 
v_i_boxed_5941_ = lean_unbox_usize(v_i_5938_);
lean_dec(v_i_5938_);
v_stop_boxed_5942_ = lean_unbox_usize(v_stop_5939_);
lean_dec(v_stop_5939_);
v_res_5943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5936_, v_as_5937_, v_i_boxed_5941_, v_stop_boxed_5942_, v_b_5940_);
lean_dec_ref(v_as_5937_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5944_, lean_object* v_f_5945_, lean_object* v_b_5946_){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; uint8_t v___x_5950_; 
v___x_5947_ = l_Lean_Syntax_getArgs(v_s_5944_);
v___x_5948_ = lean_unsigned_to_nat(0u);
v___x_5949_ = lean_array_get_size(v___x_5947_);
v___x_5950_ = lean_nat_dec_lt(v___x_5948_, v___x_5949_);
if (v___x_5950_ == 0)
{
lean_dec_ref(v___x_5947_);
lean_dec(v_f_5945_);
return v_b_5946_;
}
else
{
size_t v___x_5951_; size_t v___x_5952_; lean_object* v___x_5953_; 
v___x_5951_ = ((size_t)0ULL);
v___x_5952_ = lean_usize_of_nat(v___x_5949_);
v___x_5953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5945_, v___x_5947_, v___x_5951_, v___x_5952_, v_b_5946_);
lean_dec_ref(v___x_5947_);
return v___x_5953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5954_, lean_object* v_f_5955_, lean_object* v_b_5956_){
_start:
{
lean_object* v_res_5957_; 
v_res_5957_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5954_, v_f_5955_, v_b_5956_);
lean_dec(v_s_5954_);
return v_res_5957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5958_, lean_object* v_f_5959_, lean_object* v_b_5960_){
_start:
{
lean_object* v___f_5961_; lean_object* v___x_5962_; 
v___f_5961_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5961_, 0, v_f_5959_);
v___x_5962_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5958_, v___f_5961_, v_b_5960_);
return v___x_5962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_5963_, lean_object* v_f_5964_, lean_object* v_b_5965_){
_start:
{
lean_object* v_res_5966_; 
v_res_5966_ = l_Lean_Syntax_foldArgs___redArg(v_s_5963_, v_f_5964_, v_b_5965_);
lean_dec(v_s_5963_);
return v_res_5966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_5967_, lean_object* v_s_5968_, lean_object* v_f_5969_, lean_object* v_b_5970_){
_start:
{
lean_object* v___x_5971_; 
v___x_5971_ = l_Lean_Syntax_foldArgs___redArg(v_s_5968_, v_f_5969_, v_b_5970_);
return v___x_5971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_5972_, lean_object* v_s_5973_, lean_object* v_f_5974_, lean_object* v_b_5975_){
_start:
{
lean_object* v_res_5976_; 
v_res_5976_ = l_Lean_Syntax_foldArgs(v_00_u03b2_5972_, v_s_5973_, v_f_5974_, v_b_5975_);
lean_dec(v_s_5973_);
return v_res_5976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_5977_, lean_object* v_s_5978_, lean_object* v_f_5979_, lean_object* v_b_5980_){
_start:
{
lean_object* v___x_5981_; 
v___x_5981_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5978_, v_f_5979_, v_b_5980_);
return v___x_5981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_5982_, lean_object* v_s_5983_, lean_object* v_f_5984_, lean_object* v_b_5985_){
_start:
{
lean_object* v_res_5986_; 
v_res_5986_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_5982_, v_s_5983_, v_f_5984_, v_b_5985_);
lean_dec(v_s_5983_);
return v_res_5986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_5987_, lean_object* v_f_5988_, lean_object* v_as_5989_, size_t v_i_5990_, size_t v_stop_5991_, lean_object* v_b_5992_){
_start:
{
lean_object* v___x_5993_; 
v___x_5993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5988_, v_as_5989_, v_i_5990_, v_stop_5991_, v_b_5992_);
return v___x_5993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5994_, lean_object* v_f_5995_, lean_object* v_as_5996_, lean_object* v_i_5997_, lean_object* v_stop_5998_, lean_object* v_b_5999_){
_start:
{
size_t v_i_boxed_6000_; size_t v_stop_boxed_6001_; lean_object* v_res_6002_; 
v_i_boxed_6000_ = lean_unbox_usize(v_i_5997_);
lean_dec(v_i_5997_);
v_stop_boxed_6001_ = lean_unbox_usize(v_stop_5998_);
lean_dec(v_stop_5998_);
v_res_6002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_5994_, v_f_5995_, v_as_5996_, v_i_boxed_6000_, v_stop_boxed_6001_, v_b_5999_);
lean_dec_ref(v_as_5996_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_6003_, lean_object* v_s_6004_, lean_object* v_x_6005_){
_start:
{
lean_object* v___x_6006_; 
v___x_6006_ = lean_apply_1(v_f_6003_, v_s_6004_);
return v___x_6006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_6007_, lean_object* v_s_6008_, lean_object* v_f_6009_){
_start:
{
lean_object* v___f_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; 
v___f_6010_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6010_, 0, v_f_6009_);
v___x_6011_ = lean_box(0);
v___x_6012_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6007_, v_s_6008_, v___f_6010_, v___x_6011_);
return v___x_6012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_6013_, lean_object* v_s_6014_, lean_object* v_f_6015_){
_start:
{
lean_object* v_res_6016_; 
v_res_6016_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6013_, v_s_6014_, v_f_6015_);
lean_dec(v_s_6014_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_6017_, lean_object* v_inst_6018_, lean_object* v_s_6019_, lean_object* v_f_6020_){
_start:
{
lean_object* v___x_6021_; 
v___x_6021_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6018_, v_s_6019_, v_f_6020_);
return v___x_6021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_6022_, lean_object* v_inst_6023_, lean_object* v_s_6024_, lean_object* v_f_6025_){
_start:
{
lean_object* v_res_6026_; 
v_res_6026_ = l_Lean_Syntax_forArgsM(v_m_6022_, v_inst_6023_, v_s_6024_, v_f_6025_);
lean_dec(v_s_6024_);
return v_res_6026_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
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
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
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
res = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension);
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_antiquotNestedExpr = _init_l_Lean_Parser_antiquotNestedExpr();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr);
l_Lean_Parser_antiquotExpr = _init_l_Lean_Parser_antiquotExpr();
lean_mark_persistent(l_Lean_Parser_antiquotExpr);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
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
l_Lean_Parser_withForbiddens___auto__1 = _init_l_Lean_Parser_withForbiddens___auto__1();
lean_mark_persistent(l_Lean_Parser_withForbiddens___auto__1);
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
