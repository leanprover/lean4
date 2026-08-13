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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t v_x_17__boxed_591_; uint8_t v_y_18__boxed_592_; uint8_t v_res_593_; lean_object* v_r_594_; 
v_x_17__boxed_591_ = lean_unbox(v_x_589_);
v_y_18__boxed_592_ = lean_unbox(v_y_590_);
v_res_593_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_17__boxed_591_, v_y_18__boxed_592_);
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
lean_object* v_stxStack_638_; lean_object* v_pos_639_; lean_object* v_pBack_640_; lean_object* v___y_642_; lean_object* v___y_646_; uint8_t v___y_656_; lean_object* v___y_657_; uint8_t v___y_658_; uint8_t v___y_664_; uint8_t v___x_677_; uint8_t v___x_678_; 
v_stxStack_638_ = lean_ctor_get(v_s_636_, 0);
lean_inc_ref(v_stxStack_638_);
v_pos_639_ = lean_ctor_get(v_s_636_, 2);
lean_inc(v_pos_639_);
v_pBack_640_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_638_);
lean_dec_ref(v_stxStack_638_);
v___x_677_ = 0;
v___x_678_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_631_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = l_Lean_Parser_ParserState_stackSize(v_s_636_);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_iniSz_635_, v___x_680_);
v___x_682_ = lean_nat_dec_eq(v___x_679_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
if (v___x_682_ == 0)
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
v___y_664_ = v___x_678_;
goto v___jp_663_;
}
}
else
{
v___y_664_ = v___x_678_;
goto v___jp_663_;
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
lean_object* v_stxStack_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_stxStack_647_ = lean_ctor_get(v___y_646_, 0);
v___x_648_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_647_);
lean_inc(v___x_648_);
v___x_649_ = l_Lean_Syntax_isAntiquots(v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v___x_648_);
v___y_642_ = v___y_646_;
goto v___jp_641_;
}
else
{
lean_object* v_s_650_; lean_object* v_s_651_; lean_object* v_s_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_pos_639_);
v_s_650_ = l_Lean_Parser_ParserState_popSyntax(v___y_646_);
v_s_651_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_640_, v_s_650_);
v_s_652_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_648_, v_s_651_);
v___x_653_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_654_ = l_Lean_Parser_ParserState_mkNode(v_s_652_, v___x_653_, v_iniSz_635_);
lean_dec(v_iniSz_635_);
return v___x_654_;
}
}
v___jp_655_:
{
if (v___y_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_659_ = l_Lean_Parser_ParserState_stackSize(v___y_657_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_iniSz_635_, v___x_660_);
v___x_662_ = lean_nat_dec_eq(v___x_659_, v___x_661_);
lean_dec(v___x_661_);
lean_dec(v___x_659_);
if (v___x_662_ == 0)
{
if (v___y_656_ == 0)
{
v___y_646_ = v___y_657_;
goto v___jp_645_;
}
else
{
v___y_642_ = v___y_657_;
goto v___jp_641_;
}
}
else
{
v___y_646_ = v___y_657_;
goto v___jp_645_;
}
}
else
{
v___y_642_ = v___y_657_;
goto v___jp_641_;
}
}
v___jp_663_:
{
if (v___y_664_ == 0)
{
uint8_t v___x_665_; 
lean_inc(v_pBack_640_);
v___x_665_ = l_Lean_Syntax_isAntiquots(v_pBack_640_);
if (v___x_665_ == 0)
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
lean_object* v_s_666_; lean_object* v_s_667_; lean_object* v_pos_668_; lean_object* v_errorMsg_669_; uint8_t v___x_670_; 
v_s_666_ = l_Lean_Parser_ParserState_restore(v_s_636_, v_iniSz_635_, v_pos_634_);
v_s_667_ = lean_apply_2(v_q_630_, v_c_632_, v_s_666_);
v_pos_668_ = lean_ctor_get(v_s_667_, 2);
lean_inc(v_pos_668_);
v_errorMsg_669_ = lean_ctor_get(v_s_667_, 4);
lean_inc(v_errorMsg_669_);
v___x_670_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_669_, v_errorMsg_637_);
lean_dec(v_errorMsg_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_pos_668_);
v___x_671_ = l_Lean_Parser_ParserState_restore(v_s_667_, v_iniSz_635_, v_pos_639_);
lean_dec(v_iniSz_635_);
v___x_672_ = l_Lean_Parser_ParserState_pushSyntax(v___x_671_, v_pBack_640_);
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_pos_639_, v_pos_668_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_lt(v_pos_668_, v_pos_639_);
lean_dec(v_pos_668_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 2;
v___x_676_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_631_, v___x_675_);
if (v___x_676_ == 0)
{
v___y_656_ = v___x_670_;
v___y_657_ = v_s_667_;
v___y_658_ = v___x_670_;
goto v___jp_655_;
}
else
{
v___y_656_ = v___x_670_;
v___y_657_ = v_s_667_;
v___y_658_ = v___x_674_;
goto v___jp_655_;
}
}
else
{
v___y_656_ = v___x_670_;
v___y_657_ = v_s_667_;
v___y_658_ = v___x_674_;
goto v___jp_655_;
}
}
else
{
lean_dec(v_pos_668_);
lean_dec(v_pBack_640_);
lean_dec(v_pos_639_);
lean_dec(v_iniSz_635_);
return v_s_667_;
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
lean_object* v_pos_683_; lean_object* v_val_684_; uint8_t v___x_685_; 
v_pos_683_ = lean_ctor_get(v_s_636_, 2);
lean_inc(v_pos_683_);
v_val_684_ = lean_ctor_get(v_errorMsg_637_, 0);
lean_inc(v_val_684_);
lean_dec_ref_known(v_errorMsg_637_, 1);
v___x_685_ = lean_nat_dec_eq(v_pos_683_, v_pos_634_);
lean_dec(v_pos_683_);
if (v___x_685_ == 0)
{
lean_dec(v_val_684_);
lean_dec(v_iniSz_635_);
lean_dec(v_pos_634_);
lean_dec_ref(v_c_632_);
lean_dec_ref(v_q_630_);
return v_s_636_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_inc(v_pos_634_);
v___x_686_ = l_Lean_Parser_ParserState_restore(v_s_636_, v_iniSz_635_, v_pos_634_);
lean_dec(v_iniSz_635_);
v___x_687_ = lean_apply_2(v_q_630_, v_c_632_, v___x_686_);
v___x_688_ = l_Lean_Parser_mergeOrElseErrors(v___x_687_, v_val_684_, v_pos_634_, v___x_685_);
lean_dec(v_pos_634_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_689_, lean_object* v_q_690_, lean_object* v_antiquotBehavior_691_, lean_object* v_c_692_, lean_object* v_s_693_){
_start:
{
uint8_t v_antiquotBehavior_boxed_694_; lean_object* v_res_695_; 
v_antiquotBehavior_boxed_694_ = lean_unbox(v_antiquotBehavior_691_);
v_res_695_ = l_Lean_Parser_orelseFnCore(v_p_689_, v_q_690_, v_antiquotBehavior_boxed_694_, v_c_692_, v_s_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_696_, lean_object* v_q_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_700_ = 2;
v___x_701_ = l_Lean_Parser_orelseFnCore(v_p_696_, v_q_697_, v___x_700_, v_a_698_, v_a_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_702_, lean_object* v_q_703_){
_start:
{
lean_object* v_collectTokens_704_; lean_object* v_collectKinds_705_; lean_object* v_firstTokens_706_; lean_object* v_collectTokens_707_; lean_object* v_collectKinds_708_; lean_object* v_firstTokens_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_719_; 
v_collectTokens_704_ = lean_ctor_get(v_p_702_, 0);
lean_inc_ref(v_collectTokens_704_);
v_collectKinds_705_ = lean_ctor_get(v_p_702_, 1);
lean_inc_ref(v_collectKinds_705_);
v_firstTokens_706_ = lean_ctor_get(v_p_702_, 2);
lean_inc(v_firstTokens_706_);
lean_dec_ref(v_p_702_);
v_collectTokens_707_ = lean_ctor_get(v_q_703_, 0);
v_collectKinds_708_ = lean_ctor_get(v_q_703_, 1);
v_firstTokens_709_ = lean_ctor_get(v_q_703_, 2);
v_isSharedCheck_719_ = !lean_is_exclusive(v_q_703_);
if (v_isSharedCheck_719_ == 0)
{
v___x_711_ = v_q_703_;
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_firstTokens_709_);
lean_inc(v_collectKinds_708_);
lean_inc(v_collectTokens_707_);
lean_dec(v_q_703_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___f_713_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_713_, 0, v_collectKinds_708_);
lean_closure_set(v___f_713_, 1, v_collectKinds_705_);
v___f_714_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_714_, 0, v_collectTokens_707_);
lean_closure_set(v___f_714_, 1, v_collectTokens_704_);
v___x_715_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_706_, v_firstTokens_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v___x_715_);
lean_ctor_set(v___x_711_, 1, v___f_713_);
lean_ctor_set(v___x_711_, 0, v___f_714_);
v___x_717_ = v___x_711_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___f_714_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___f_713_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_720_, lean_object* v_p2_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_box(0);
v___x_725_ = lean_apply_1(v_p2_721_, v___x_724_);
v___x_726_ = l_Lean_Parser_orelseFn(v_p1_720_, v___x_725_, v___y_722_, v___y_723_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_729_, lean_object* v_q_730_){
_start:
{
lean_object* v_info_731_; lean_object* v_fn_732_; lean_object* v_info_733_; lean_object* v_fn_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_743_; 
v_info_731_ = lean_ctor_get(v_p_729_, 0);
lean_inc_ref(v_info_731_);
v_fn_732_ = lean_ctor_get(v_p_729_, 1);
lean_inc_ref(v_fn_732_);
lean_dec_ref(v_p_729_);
v_info_733_ = lean_ctor_get(v_q_730_, 0);
v_fn_734_ = lean_ctor_get(v_q_730_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_q_730_);
if (v_isSharedCheck_743_ == 0)
{
v___x_736_ = v_q_730_;
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_fn_734_);
lean_inc(v_info_733_);
lean_dec(v_q_730_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_738_ = l_Lean_Parser_orelseInfo(v_info_731_, v_info_733_);
v___x_739_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_739_, 0, v_fn_732_);
lean_closure_set(v___x_739_, 1, v_fn_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_739_);
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_752_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_753_ = l_Lean_addBuiltinDocString(v___x_751_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_756_, lean_object* v_b_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = lean_box(0);
v___x_759_ = lean_apply_1(v_b_757_, v___x_758_);
v___x_760_ = l_Lean_Parser_orelse(v_a_756_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_763_){
_start:
{
lean_object* v_collectTokens_764_; lean_object* v_collectKinds_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_collectTokens_764_ = lean_ctor_get(v_info_763_, 0);
v_collectKinds_765_ = lean_ctor_get(v_info_763_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_info_763_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_info_763_, 2);
lean_dec(v_unused_774_);
v___x_767_ = v_info_763_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_collectKinds_765_);
lean_inc(v_collectTokens_764_);
lean_dec(v_info_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_box(1);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 2, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_collectTokens_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_collectKinds_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_775_, lean_object* v_c_776_, lean_object* v_s_777_){
_start:
{
lean_object* v_pos_778_; lean_object* v___x_779_; lean_object* v_errorMsg_780_; 
v_pos_778_ = lean_ctor_get(v_s_777_, 2);
lean_inc(v_pos_778_);
v___x_779_ = lean_apply_2(v_p_775_, v_c_776_, v_s_777_);
v_errorMsg_780_ = lean_ctor_get(v___x_779_, 4);
lean_inc(v_errorMsg_780_);
if (lean_obj_tag(v_errorMsg_780_) == 1)
{
lean_object* v_stxStack_781_; lean_object* v_lhsPrec_782_; lean_object* v_cache_783_; lean_object* v_recoveredErrors_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_stxStack_781_ = lean_ctor_get(v___x_779_, 0);
v_lhsPrec_782_ = lean_ctor_get(v___x_779_, 1);
v_cache_783_ = lean_ctor_get(v___x_779_, 3);
v_recoveredErrors_784_ = lean_ctor_get(v___x_779_, 5);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_792_ = lean_ctor_get(v___x_779_, 4);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v___x_779_, 2);
lean_dec(v_unused_793_);
v___x_786_ = v___x_779_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_recoveredErrors_784_);
lean_inc(v_cache_783_);
lean_inc(v_lhsPrec_782_);
lean_inc(v_stxStack_781_);
lean_dec(v___x_779_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 2, v_pos_778_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_stxStack_781_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_lhsPrec_782_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_pos_778_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_cache_783_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_errorMsg_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 5, v_recoveredErrors_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_dec(v_errorMsg_780_);
lean_dec(v_pos_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_794_){
_start:
{
lean_object* v_info_795_; lean_object* v_fn_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
v_info_795_ = lean_ctor_get(v_p_794_, 0);
v_fn_796_ = lean_ctor_get(v_p_794_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_p_794_);
if (v_isSharedCheck_804_ == 0)
{
v___x_798_ = v_p_794_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_fn_796_);
lean_inc(v_info_795_);
lean_dec(v_p_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_800_, 0, v_fn_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_info_795_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_813_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_814_ = l_Lean_addBuiltinDocString(v___x_812_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_816_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_initialPos_819_; lean_object* v_initialSize_820_; lean_object* v_initialPos_821_; lean_object* v_initialSize_822_; uint8_t v___x_823_; 
v_initialPos_819_ = lean_ctor_get(v_x_817_, 0);
v_initialSize_820_ = lean_ctor_get(v_x_817_, 1);
v_initialPos_821_ = lean_ctor_get(v_x_818_, 0);
v_initialSize_822_ = lean_ctor_get(v_x_818_, 1);
v___x_823_ = lean_nat_dec_eq(v_initialPos_819_, v_initialPos_821_);
if (v___x_823_ == 0)
{
return v___x_823_;
}
else
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_eq(v_initialSize_820_, v_initialSize_822_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_825_, v_x_826_);
lean_dec_ref(v_x_826_);
lean_dec_ref(v_x_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_initialPos_833_; lean_object* v_initialSize_834_; lean_object* v_initialPos_835_; lean_object* v_initialSize_836_; uint8_t v___x_837_; 
v_initialPos_833_ = lean_ctor_get(v_x_831_, 0);
v_initialSize_834_ = lean_ctor_get(v_x_831_, 1);
v_initialPos_835_ = lean_ctor_get(v_x_832_, 0);
v_initialSize_836_ = lean_ctor_get(v_x_832_, 1);
v___x_837_ = lean_nat_dec_eq(v_initialPos_833_, v_initialPos_835_);
if (v___x_837_ == 0)
{
return v___x_837_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_eq(v_initialSize_834_, v_initialSize_836_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_839_, v_x_840_);
lean_dec_ref(v_x_840_);
lean_dec_ref(v_x_839_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_846_, v_x_847_);
lean_dec_ref(v_x_847_);
lean_dec_ref(v_x_846_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(14u);
v___x_864_ = lean_nat_to_int(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(15u);
v___x_878_ = lean_nat_to_int(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_880_ = lean_string_length(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_882_ = lean_nat_to_int(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_885_){
_start:
{
lean_object* v_initialPos_886_; lean_object* v_initialSize_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_925_; 
v_initialPos_886_ = lean_ctor_get(v_x_885_, 0);
v_initialSize_887_ = lean_ctor_get(v_x_885_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_x_885_);
if (v_isSharedCheck_925_ == 0)
{
v___x_889_ = v_x_885_;
v_isShared_890_ = v_isSharedCheck_925_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_initialSize_887_);
lean_inc(v_initialPos_886_);
lean_dec(v_x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_925_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_891_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_892_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_893_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_894_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_895_ = l_Nat_reprFast(v_initialPos_886_);
v___x_896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 5);
lean_ctor_set(v___x_889_, 1, v___x_896_);
lean_ctor_set(v___x_889_, 0, v___x_894_);
v___x_898_ = v___x_889_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_924_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_899_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_893_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = 0;
v___x_903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_902_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_892_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_box(1);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_891_);
v___x_912_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_913_ = l_Nat_reprFast(v_initialSize_887_);
v___x_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_912_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set_uint8(v___x_916_, sizeof(void*)*1, v___x_902_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_911_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_919_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_917_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_899_);
v___x_922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1, v___x_902_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_926_, lean_object* v_prec_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_929_, lean_object* v_prec_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_929_, v_prec_930_);
lean_dec(v_prec_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_934_, lean_object* v_recover_935_, lean_object* v_c_936_, lean_object* v_s_937_){
_start:
{
lean_object* v_stxStack_938_; lean_object* v_pos_939_; lean_object* v_s_940_; lean_object* v_errorMsg_941_; 
v_stxStack_938_ = lean_ctor_get(v_s_937_, 0);
lean_inc_ref(v_stxStack_938_);
v_pos_939_ = lean_ctor_get(v_s_937_, 2);
lean_inc(v_pos_939_);
lean_inc_ref(v_c_936_);
v_s_940_ = lean_apply_2(v_p_934_, v_c_936_, v_s_937_);
v_errorMsg_941_ = lean_ctor_get(v_s_940_, 4);
lean_inc(v_errorMsg_941_);
if (lean_obj_tag(v_errorMsg_941_) == 1)
{
lean_object* v_stxStack_942_; lean_object* v_lhsPrec_943_; lean_object* v_pos_944_; lean_object* v_cache_945_; lean_object* v_recoveredErrors_946_; lean_object* v_val_947_; lean_object* v_iniSz_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_s_x27_952_; lean_object* v_stxStack_953_; lean_object* v_pos_954_; lean_object* v_errorMsg_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_966_; 
v_stxStack_942_ = lean_ctor_get(v_s_940_, 0);
lean_inc_ref(v_stxStack_942_);
v_lhsPrec_943_ = lean_ctor_get(v_s_940_, 1);
lean_inc_n(v_lhsPrec_943_, 2);
v_pos_944_ = lean_ctor_get(v_s_940_, 2);
lean_inc(v_pos_944_);
v_cache_945_ = lean_ctor_get(v_s_940_, 3);
lean_inc_ref_n(v_cache_945_, 2);
v_recoveredErrors_946_ = lean_ctor_get(v_s_940_, 5);
lean_inc_ref_n(v_recoveredErrors_946_, 2);
v_val_947_ = lean_ctor_get(v_errorMsg_941_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v_errorMsg_941_, 1);
v_iniSz_948_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_938_);
lean_dec_ref(v_stxStack_938_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_pos_939_);
lean_ctor_set(v___x_949_, 1, v_iniSz_948_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_951_, 0, v_stxStack_942_);
lean_ctor_set(v___x_951_, 1, v_lhsPrec_943_);
lean_ctor_set(v___x_951_, 2, v_pos_944_);
lean_ctor_set(v___x_951_, 3, v_cache_945_);
lean_ctor_set(v___x_951_, 4, v___x_950_);
lean_ctor_set(v___x_951_, 5, v_recoveredErrors_946_);
v_s_x27_952_ = lean_apply_3(v_recover_935_, v___x_949_, v_c_936_, v___x_951_);
v_stxStack_953_ = lean_ctor_get(v_s_x27_952_, 0);
v_pos_954_ = lean_ctor_get(v_s_x27_952_, 2);
v_errorMsg_955_ = lean_ctor_get(v_s_x27_952_, 4);
v_isSharedCheck_966_ = !lean_is_exclusive(v_s_x27_952_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_967_ = lean_ctor_get(v_s_x27_952_, 5);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_s_x27_952_, 3);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_s_x27_952_, 1);
lean_dec(v_unused_969_);
v___x_957_ = v_s_x27_952_;
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_errorMsg_955_);
lean_inc(v_pos_954_);
lean_inc(v_stxStack_953_);
lean_dec(v_s_x27_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; 
v___x_959_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_955_, v___x_950_);
lean_dec(v_errorMsg_955_);
if (v___x_959_ == 0)
{
lean_del_object(v___x_957_);
lean_dec(v_pos_954_);
lean_dec_ref(v_stxStack_953_);
lean_dec(v_val_947_);
lean_dec_ref(v_recoveredErrors_946_);
lean_dec_ref(v_cache_945_);
lean_dec(v_lhsPrec_943_);
return v_s_940_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
lean_dec_ref(v_s_940_);
lean_inc_ref(v_stxStack_953_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_stxStack_953_);
lean_ctor_set(v___x_960_, 1, v_val_947_);
lean_inc(v_pos_954_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v_pos_954_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_array_push(v_recoveredErrors_946_, v___x_961_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 5, v___x_962_);
lean_ctor_set(v___x_957_, 4, v___x_950_);
lean_ctor_set(v___x_957_, 3, v_cache_945_);
lean_ctor_set(v___x_957_, 1, v_lhsPrec_943_);
v___x_964_ = v___x_957_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_stxStack_953_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_lhsPrec_943_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_pos_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_cache_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_dec(v_errorMsg_941_);
lean_dec(v_pos_939_);
lean_dec_ref(v_stxStack_938_);
lean_dec_ref(v_c_936_);
lean_dec_ref(v_recover_935_);
return v_s_940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_970_, lean_object* v_s_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_974_; lean_object* v_fn_975_; lean_object* v___x_976_; 
v___x_974_ = lean_apply_1(v_handler_970_, v_s_971_);
v_fn_975_ = lean_ctor_get(v___x_974_, 1);
lean_inc_ref(v_fn_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = lean_apply_2(v_fn_975_, v___y_972_, v___y_973_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_977_, lean_object* v_handler_978_){
_start:
{
lean_object* v_info_979_; lean_object* v_fn_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
v_info_979_ = lean_ctor_get(v_parser_977_, 0);
v_fn_980_ = lean_ctor_get(v_parser_977_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_parser_977_);
if (v_isSharedCheck_989_ == 0)
{
v___x_982_ = v_parser_977_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_fn_980_);
lean_inc(v_info_979_);
lean_dec(v_parser_977_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_984_, 0, v_handler_978_);
v___x_985_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_985_, 0, v_fn_980_);
lean_closure_set(v___x_985_, 1, v___f_984_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_info_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_998_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_999_ = l_Lean_addBuiltinDocString(v___x_997_, v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_1002_, lean_object* v_x_1003_){
_start:
{
lean_inc_ref(v_handler_1002_);
return v_handler_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Parser_recover___lam__0(v_handler_1004_, v_x_1005_);
lean_dec_ref(v_x_1005_);
lean_dec_ref(v_handler_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1007_, lean_object* v_handler_1008_){
_start:
{
lean_object* v___f_1009_; lean_object* v___x_1010_; 
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1009_, 0, v_handler_1008_);
v___x_1010_ = l_Lean_Parser_recover_x27(v_parser_1007_, v___f_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1019_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1020_ = l_Lean_addBuiltinDocString(v___x_1018_, v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1026_, lean_object* v_c_1027_, lean_object* v_s_1028_){
_start:
{
lean_object* v_pos_1029_; lean_object* v_iniSz_1030_; lean_object* v___y_1032_; lean_object* v_s_1035_; lean_object* v_pos_1036_; lean_object* v_errorMsg_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_pos_1029_ = lean_ctor_get(v_s_1028_, 2);
lean_inc(v_pos_1029_);
v_iniSz_1030_ = l_Lean_Parser_ParserState_stackSize(v_s_1028_);
v_s_1035_ = lean_apply_2(v_p_1026_, v_c_1027_, v_s_1028_);
v_pos_1036_ = lean_ctor_get(v_s_1035_, 2);
lean_inc(v_pos_1036_);
v_errorMsg_1037_ = lean_ctor_get(v_s_1035_, 4);
lean_inc(v_errorMsg_1037_);
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1037_, v___x_1038_);
lean_dec(v_errorMsg_1037_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_nat_dec_eq(v_pos_1036_, v_pos_1029_);
lean_dec(v_pos_1036_);
if (v___x_1040_ == 0)
{
lean_dec(v_pos_1029_);
v___y_1032_ = v_s_1035_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Parser_ParserState_restore(v_s_1035_, v_iniSz_1030_, v_pos_1029_);
v___y_1032_ = v___x_1041_;
goto v___jp_1031_;
}
}
else
{
lean_dec(v_pos_1036_);
lean_dec(v_pos_1029_);
v___y_1032_ = v_s_1035_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1034_ = l_Lean_Parser_ParserState_mkNode(v___y_1032_, v___x_1033_, v_iniSz_1030_);
lean_dec(v_iniSz_1030_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1042_){
_start:
{
lean_object* v_collectTokens_1043_; lean_object* v_collectKinds_1044_; lean_object* v_firstTokens_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_collectTokens_1043_ = lean_ctor_get(v_p_1042_, 0);
v_collectKinds_1044_ = lean_ctor_get(v_p_1042_, 1);
v_firstTokens_1045_ = lean_ctor_get(v_p_1042_, 2);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_p_1042_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1047_ = v_p_1042_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_firstTokens_1045_);
lean_inc(v_collectKinds_1044_);
lean_inc(v_collectTokens_1043_);
lean_dec(v_p_1042_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 2, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_collectTokens_1043_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_collectKinds_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1054_){
_start:
{
lean_object* v_info_1055_; lean_object* v_fn_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1065_; 
v_info_1055_ = lean_ctor_get(v_p_1054_, 0);
v_fn_1056_ = lean_ctor_get(v_p_1054_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_p_1054_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1058_ = v_p_1054_;
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_fn_1056_);
lean_inc(v_info_1055_);
lean_dec(v_p_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1060_ = l_Lean_Parser_optionalInfo(v_info_1055_);
v___x_1061_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1061_, 0, v_fn_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1061_);
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1066_, lean_object* v_c_1067_, lean_object* v_s_1068_){
_start:
{
lean_object* v_pos_1069_; lean_object* v_iniSz_1070_; lean_object* v_s_1071_; lean_object* v_errorMsg_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_pos_1069_ = lean_ctor_get(v_s_1068_, 2);
lean_inc(v_pos_1069_);
v_iniSz_1070_ = l_Lean_Parser_ParserState_stackSize(v_s_1068_);
v_s_1071_ = lean_apply_2(v_p_1066_, v_c_1067_, v_s_1068_);
v_errorMsg_1072_ = lean_ctor_get(v_s_1071_, 4);
lean_inc(v_errorMsg_1072_);
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1072_, v___x_1073_);
lean_dec(v_errorMsg_1072_);
if (v___x_1074_ == 0)
{
lean_dec(v_iniSz_1070_);
lean_dec(v_pos_1069_);
return v_s_1071_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Parser_ParserState_restore(v_s_1071_, v_iniSz_1070_, v_pos_1069_);
lean_dec(v_iniSz_1070_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1076_){
_start:
{
lean_object* v_info_1077_; lean_object* v_fn_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_info_1077_ = lean_ctor_get(v_p_1076_, 0);
v_fn_1078_ = lean_ctor_get(v_p_1076_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_p_1076_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v_p_1076_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_fn_1078_);
lean_inc(v_info_1077_);
lean_dec(v_p_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1082_, 0, v_fn_1078_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_info_1077_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1095_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1096_ = l_Lean_addBuiltinDocString(v___x_1094_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1100_, lean_object* v_msg_1101_, lean_object* v_c_1102_, lean_object* v_s_1103_){
_start:
{
lean_object* v_pos_1104_; lean_object* v_iniSz_1105_; lean_object* v_s_1106_; lean_object* v_errorMsg_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_pos_1104_ = lean_ctor_get(v_s_1103_, 2);
lean_inc(v_pos_1104_);
v_iniSz_1105_ = l_Lean_Parser_ParserState_stackSize(v_s_1103_);
v_s_1106_ = lean_apply_2(v_p_1100_, v_c_1102_, v_s_1103_);
v_errorMsg_1107_ = lean_ctor_get(v_s_1106_, 4);
lean_inc(v_errorMsg_1107_);
v___x_1108_ = lean_box(0);
v___x_1109_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1107_, v___x_1108_);
lean_dec(v_errorMsg_1107_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Parser_ParserState_restore(v_s_1106_, v_iniSz_1105_, v_pos_1104_);
lean_dec(v_iniSz_1105_);
return v___x_1110_;
}
else
{
lean_object* v_s_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_s_1111_ = l_Lean_Parser_ParserState_restore(v_s_1106_, v_iniSz_1105_, v_pos_1104_);
lean_dec(v_iniSz_1105_);
v___x_1112_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1113_ = lean_string_append(v___x_1112_, v_msg_1101_);
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1111_, v___x_1113_, v___x_1114_, v___x_1109_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1116_, lean_object* v_msg_1117_, lean_object* v_c_1118_, lean_object* v_s_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Parser_notFollowedByFn(v_p_1116_, v_msg_1117_, v_c_1118_, v_s_1119_);
lean_dec_ref(v_msg_1117_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1121_, lean_object* v_msg_1122_){
_start:
{
lean_object* v_fn_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v_fn_1123_ = lean_ctor_get(v_p_1121_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_p_1121_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_p_1121_, 0);
lean_dec(v_unused_1133_);
v___x_1125_ = v_p_1121_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_fn_1123_);
lean_dec(v_p_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1128_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1128_, 0, v_fn_1123_);
lean_closure_set(v___x_1128_, 1, v_msg_1122_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1128_);
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1142_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1143_ = l_Lean_addBuiltinDocString(v___x_1141_, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1147_, lean_object* v_c_1148_, lean_object* v_s_1149_){
_start:
{
lean_object* v_pos_1150_; lean_object* v_iniSz_1151_; lean_object* v_s_1152_; lean_object* v_pos_1153_; lean_object* v_errorMsg_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_pos_1150_ = lean_ctor_get(v_s_1149_, 2);
lean_inc(v_pos_1150_);
v_iniSz_1151_ = l_Lean_Parser_ParserState_stackSize(v_s_1149_);
lean_inc_ref(v_p_1147_);
lean_inc_ref(v_c_1148_);
v_s_1152_ = lean_apply_2(v_p_1147_, v_c_1148_, v_s_1149_);
v_pos_1153_ = lean_ctor_get(v_s_1152_, 2);
lean_inc(v_pos_1153_);
v_errorMsg_1154_ = lean_ctor_get(v_s_1152_, 4);
lean_inc(v_errorMsg_1154_);
v___x_1155_ = lean_box(0);
v___x_1156_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1154_, v___x_1155_);
lean_dec(v_errorMsg_1154_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; 
lean_dec_ref(v_c_1148_);
lean_dec_ref(v_p_1147_);
v___x_1157_ = lean_nat_dec_eq(v_pos_1150_, v_pos_1153_);
lean_dec(v_pos_1153_);
if (v___x_1157_ == 0)
{
lean_dec(v_iniSz_1151_);
lean_dec(v_pos_1150_);
return v_s_1152_;
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Parser_ParserState_restore(v_s_1152_, v_iniSz_1151_, v_pos_1150_);
lean_dec(v_iniSz_1151_);
return v___x_1158_;
}
}
else
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_nat_dec_eq(v_pos_1150_, v_pos_1153_);
lean_dec(v_pos_1153_);
lean_dec(v_pos_1150_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_iniSz_1151_, v___x_1160_);
v___x_1162_ = l_Lean_Parser_ParserState_stackSize(v_s_1152_);
v___x_1163_ = lean_nat_dec_lt(v___x_1161_, v___x_1162_);
lean_dec(v___x_1162_);
lean_dec(v___x_1161_);
if (v___x_1163_ == 0)
{
lean_dec(v_iniSz_1151_);
v_s_1149_ = v_s_1152_;
goto _start;
}
else
{
lean_object* v___x_1165_; lean_object* v_s_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1166_ = l_Lean_Parser_ParserState_mkNode(v_s_1152_, v___x_1165_, v_iniSz_1151_);
lean_dec(v_iniSz_1151_);
v_s_1149_ = v_s_1166_;
goto _start;
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v_iniSz_1151_);
lean_dec_ref(v_c_1148_);
lean_dec_ref(v_p_1147_);
v___x_1168_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1169_ = lean_box(0);
v___x_1170_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1152_, v___x_1168_, v___x_1169_, v___x_1156_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1171_, lean_object* v_c_1172_, lean_object* v_s_1173_){
_start:
{
lean_object* v_iniSz_1174_; lean_object* v_s_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_iniSz_1174_ = l_Lean_Parser_ParserState_stackSize(v_s_1173_);
v_s_1175_ = l_Lean_Parser_manyAux(v_p_1171_, v_c_1172_, v_s_1173_);
v___x_1176_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1177_ = l_Lean_Parser_ParserState_mkNode(v_s_1175_, v___x_1176_, v_iniSz_1174_);
lean_dec(v_iniSz_1174_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1178_){
_start:
{
lean_object* v_info_1179_; lean_object* v_fn_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_info_1179_ = lean_ctor_get(v_p_1178_, 0);
v_fn_1180_ = lean_ctor_get(v_p_1178_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_p_1178_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v_p_1178_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_fn_1180_);
lean_inc(v_info_1179_);
lean_dec(v_p_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = l_Lean_Parser_noFirstTokenInfo(v_info_1179_);
v___x_1185_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1185_, 0, v_fn_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1185_);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1190_, lean_object* v_c_1191_, lean_object* v_s_1192_){
_start:
{
lean_object* v_iniSz_1193_; lean_object* v___x_1194_; lean_object* v_s_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_iniSz_1193_ = l_Lean_Parser_ParserState_stackSize(v_s_1192_);
lean_inc_ref(v_p_1190_);
v___x_1194_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1194_, 0, v_p_1190_);
v_s_1195_ = l_Lean_Parser_andthenFn(v_p_1190_, v___x_1194_, v_c_1191_, v_s_1192_);
v___x_1196_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1197_ = l_Lean_Parser_ParserState_mkNode(v_s_1195_, v___x_1196_, v_iniSz_1193_);
lean_dec(v_iniSz_1193_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1198_){
_start:
{
lean_object* v_info_1199_; lean_object* v_fn_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_info_1199_ = lean_ctor_get(v_p_1198_, 0);
v_fn_1200_ = lean_ctor_get(v_p_1198_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_p_1198_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1202_ = v_p_1198_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_fn_1200_);
lean_inc(v_info_1199_);
lean_dec(v_p_1198_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1204_, 0, v_fn_1200_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_info_1199_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1209_, lean_object* v_sep_1210_, uint8_t v_allowTrailingSep_1211_, lean_object* v_iniSz_1212_, uint8_t v_pOpt_1213_, lean_object* v_c_1214_, lean_object* v_s_1215_){
_start:
{
lean_object* v_s_1217_; lean_object* v_pos_1218_; lean_object* v_pos_1235_; lean_object* v_sz_1236_; lean_object* v_s_1237_; lean_object* v_pos_1238_; lean_object* v_errorMsg_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_pos_1235_ = lean_ctor_get(v_s_1215_, 2);
lean_inc(v_pos_1235_);
v_sz_1236_ = l_Lean_Parser_ParserState_stackSize(v_s_1215_);
lean_inc_ref(v_p_1209_);
lean_inc_ref(v_c_1214_);
v_s_1237_ = lean_apply_2(v_p_1209_, v_c_1214_, v_s_1215_);
v_pos_1238_ = lean_ctor_get(v_s_1237_, 2);
lean_inc(v_pos_1238_);
v_errorMsg_1239_ = lean_ctor_get(v_s_1237_, 4);
lean_inc(v_errorMsg_1239_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1239_, v___x_1240_);
lean_dec(v_errorMsg_1239_);
if (v___x_1241_ == 0)
{
uint8_t v___x_1242_; 
lean_dec_ref(v_c_1214_);
lean_dec_ref(v_sep_1210_);
lean_dec_ref(v_p_1209_);
v___x_1242_ = lean_nat_dec_lt(v_pos_1235_, v_pos_1238_);
lean_dec(v_pos_1238_);
if (v___x_1242_ == 0)
{
if (v_pOpt_1213_ == 0)
{
lean_object* v___x_1243_; lean_object* v_s_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_sz_1236_);
lean_dec(v_pos_1235_);
v___x_1243_ = lean_box(0);
v_s_1244_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1237_, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1246_ = l_Lean_Parser_ParserState_mkNode(v_s_1244_, v___x_1245_, v_iniSz_1212_);
return v___x_1246_;
}
else
{
lean_object* v_s_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_s_1247_ = l_Lean_Parser_ParserState_restore(v_s_1237_, v_sz_1236_, v_pos_1235_);
lean_dec(v_sz_1236_);
v___x_1248_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1249_ = l_Lean_Parser_ParserState_mkNode(v_s_1247_, v___x_1248_, v_iniSz_1212_);
return v___x_1249_;
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_sz_1236_);
lean_dec(v_pos_1235_);
v___x_1250_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1251_ = l_Lean_Parser_ParserState_mkNode(v_s_1237_, v___x_1250_, v_iniSz_1212_);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
lean_dec(v_pos_1235_);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_add(v_sz_1236_, v___x_1252_);
v___x_1254_ = l_Lean_Parser_ParserState_stackSize(v_s_1237_);
v___x_1255_ = lean_nat_dec_lt(v___x_1253_, v___x_1254_);
lean_dec(v___x_1254_);
lean_dec(v___x_1253_);
if (v___x_1255_ == 0)
{
lean_dec(v_sz_1236_);
v_s_1217_ = v_s_1237_;
v_pos_1218_ = v_pos_1238_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1256_; lean_object* v_s_1257_; lean_object* v_pos_1258_; 
lean_dec(v_pos_1238_);
v___x_1256_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1257_ = l_Lean_Parser_ParserState_mkNode(v_s_1237_, v___x_1256_, v_sz_1236_);
lean_dec(v_sz_1236_);
v_pos_1258_ = lean_ctor_get(v_s_1257_, 2);
lean_inc(v_pos_1258_);
v_s_1217_ = v_s_1257_;
v_pos_1218_ = v_pos_1258_;
goto v___jp_1216_;
}
}
v___jp_1216_:
{
lean_object* v_sz_1219_; lean_object* v_s_1220_; lean_object* v_errorMsg_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_sz_1219_ = l_Lean_Parser_ParserState_stackSize(v_s_1217_);
lean_inc_ref(v_sep_1210_);
lean_inc_ref(v_c_1214_);
v_s_1220_ = lean_apply_2(v_sep_1210_, v_c_1214_, v_s_1217_);
v_errorMsg_1221_ = lean_ctor_get(v_s_1220_, 4);
lean_inc(v_errorMsg_1221_);
v___x_1222_ = lean_box(0);
v___x_1223_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1221_, v___x_1222_);
lean_dec(v_errorMsg_1221_);
if (v___x_1223_ == 0)
{
lean_object* v_s_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v_c_1214_);
lean_dec_ref(v_sep_1210_);
lean_dec_ref(v_p_1209_);
v_s_1224_ = l_Lean_Parser_ParserState_restore(v_s_1220_, v_sz_1219_, v_pos_1218_);
lean_dec(v_sz_1219_);
v___x_1225_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1226_ = l_Lean_Parser_ParserState_mkNode(v_s_1224_, v___x_1225_, v_iniSz_1212_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
lean_dec(v_pos_1218_);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_sz_1219_, v___x_1227_);
v___x_1229_ = l_Lean_Parser_ParserState_stackSize(v_s_1220_);
v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
lean_dec(v___x_1229_);
lean_dec(v___x_1228_);
if (v___x_1230_ == 0)
{
lean_dec(v_sz_1219_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1211_;
lean_object* _tmp_6 = v_s_1220_;
v_pOpt_1213_ = _tmp_4;
v_s_1215_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1232_; lean_object* v_s_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1233_ = l_Lean_Parser_ParserState_mkNode(v_s_1220_, v___x_1232_, v_sz_1219_);
lean_dec(v_sz_1219_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1211_;
lean_object* _tmp_6 = v_s_1233_;
v_pOpt_1213_ = _tmp_4;
v_s_1215_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1259_, lean_object* v_sep_1260_, lean_object* v_allowTrailingSep_1261_, lean_object* v_iniSz_1262_, lean_object* v_pOpt_1263_, lean_object* v_c_1264_, lean_object* v_s_1265_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1266_; uint8_t v_pOpt_boxed_1267_; lean_object* v_res_1268_; 
v_allowTrailingSep_boxed_1266_ = lean_unbox(v_allowTrailingSep_1261_);
v_pOpt_boxed_1267_ = lean_unbox(v_pOpt_1263_);
v_res_1268_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1259_, v_sep_1260_, v_allowTrailingSep_boxed_1266_, v_iniSz_1262_, v_pOpt_boxed_1267_, v_c_1264_, v_s_1265_);
lean_dec(v_iniSz_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1269_, lean_object* v_sep_1270_, uint8_t v_allowTrailingSep_1271_, lean_object* v_iniSz_1272_, uint8_t v_pOpt_1273_, lean_object* v_c_1274_, lean_object* v_s_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1269_, v_sep_1270_, v_allowTrailingSep_1271_, v_iniSz_1272_, v_pOpt_1273_, v_c_1274_, v_s_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1277_, lean_object* v_sep_1278_, lean_object* v_allowTrailingSep_1279_, lean_object* v_iniSz_1280_, lean_object* v_pOpt_1281_, lean_object* v_c_1282_, lean_object* v_s_1283_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1284_; uint8_t v_pOpt_boxed_1285_; lean_object* v_res_1286_; 
v_allowTrailingSep_boxed_1284_ = lean_unbox(v_allowTrailingSep_1279_);
v_pOpt_boxed_1285_ = lean_unbox(v_pOpt_1281_);
v_res_1286_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1277_, v_sep_1278_, v_allowTrailingSep_boxed_1284_, v_iniSz_1280_, v_pOpt_boxed_1285_, v_c_1282_, v_s_1283_);
lean_dec(v_iniSz_1280_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1287_, lean_object* v_p_1288_, lean_object* v_sep_1289_, lean_object* v_c_1290_, lean_object* v_s_1291_){
_start:
{
lean_object* v_iniSz_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; 
v_iniSz_1292_ = l_Lean_Parser_ParserState_stackSize(v_s_1291_);
v___x_1293_ = 1;
v___x_1294_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1288_, v_sep_1289_, v_allowTrailingSep_1287_, v_iniSz_1292_, v___x_1293_, v_c_1290_, v_s_1291_);
lean_dec(v_iniSz_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1295_, lean_object* v_p_1296_, lean_object* v_sep_1297_, lean_object* v_c_1298_, lean_object* v_s_1299_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1300_; lean_object* v_res_1301_; 
v_allowTrailingSep_boxed_1300_ = lean_unbox(v_allowTrailingSep_1295_);
v_res_1301_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1300_, v_p_1296_, v_sep_1297_, v_c_1298_, v_s_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1302_, lean_object* v_p_1303_, lean_object* v_sep_1304_, lean_object* v_c_1305_, lean_object* v_s_1306_){
_start:
{
lean_object* v_iniSz_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; 
v_iniSz_1307_ = l_Lean_Parser_ParserState_stackSize(v_s_1306_);
v___x_1308_ = 0;
v___x_1309_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1303_, v_sep_1304_, v_allowTrailingSep_1302_, v_iniSz_1307_, v___x_1308_, v_c_1305_, v_s_1306_);
lean_dec(v_iniSz_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1310_, lean_object* v_p_1311_, lean_object* v_sep_1312_, lean_object* v_c_1313_, lean_object* v_s_1314_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1315_; lean_object* v_res_1316_; 
v_allowTrailingSep_boxed_1315_ = lean_unbox(v_allowTrailingSep_1310_);
v_res_1316_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1315_, v_p_1311_, v_sep_1312_, v_c_1313_, v_s_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1317_, lean_object* v_sep_1318_){
_start:
{
lean_object* v_collectTokens_1319_; lean_object* v_collectKinds_1320_; lean_object* v_collectTokens_1321_; lean_object* v_collectKinds_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1332_; 
v_collectTokens_1319_ = lean_ctor_get(v_p_1317_, 0);
lean_inc_ref(v_collectTokens_1319_);
v_collectKinds_1320_ = lean_ctor_get(v_p_1317_, 1);
lean_inc_ref(v_collectKinds_1320_);
lean_dec_ref(v_p_1317_);
v_collectTokens_1321_ = lean_ctor_get(v_sep_1318_, 0);
v_collectKinds_1322_ = lean_ctor_get(v_sep_1318_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_sep_1318_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v_sep_1318_, 2);
lean_dec(v_unused_1333_);
v___x_1324_ = v_sep_1318_;
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_collectKinds_1322_);
lean_inc(v_collectTokens_1321_);
lean_dec(v_sep_1318_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1326_, 0, v_collectKinds_1322_);
lean_closure_set(v___f_1326_, 1, v_collectKinds_1320_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1327_, 0, v_collectTokens_1321_);
lean_closure_set(v___f_1327_, 1, v_collectTokens_1319_);
v___x_1328_ = lean_box(1);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 2, v___x_1328_);
lean_ctor_set(v___x_1324_, 1, v___f_1326_);
lean_ctor_set(v___x_1324_, 0, v___f_1327_);
v___x_1330_ = v___x_1324_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___f_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___f_1326_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1334_, lean_object* v_sep_1335_){
_start:
{
lean_object* v_collectTokens_1336_; lean_object* v_collectKinds_1337_; lean_object* v_firstTokens_1338_; lean_object* v_collectTokens_1339_; lean_object* v_collectKinds_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1349_; 
v_collectTokens_1336_ = lean_ctor_get(v_p_1334_, 0);
lean_inc_ref(v_collectTokens_1336_);
v_collectKinds_1337_ = lean_ctor_get(v_p_1334_, 1);
lean_inc_ref(v_collectKinds_1337_);
v_firstTokens_1338_ = lean_ctor_get(v_p_1334_, 2);
lean_inc(v_firstTokens_1338_);
lean_dec_ref(v_p_1334_);
v_collectTokens_1339_ = lean_ctor_get(v_sep_1335_, 0);
v_collectKinds_1340_ = lean_ctor_get(v_sep_1335_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_sep_1335_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_sep_1335_, 2);
lean_dec(v_unused_1350_);
v___x_1342_ = v_sep_1335_;
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_collectKinds_1340_);
lean_inc(v_collectTokens_1339_);
lean_dec(v_sep_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___f_1344_; lean_object* v___f_1345_; lean_object* v___x_1347_; 
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1344_, 0, v_collectKinds_1340_);
lean_closure_set(v___f_1344_, 1, v_collectKinds_1337_);
v___f_1345_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1345_, 0, v_collectTokens_1339_);
lean_closure_set(v___f_1345_, 1, v_collectTokens_1336_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v_firstTokens_1338_);
lean_ctor_set(v___x_1342_, 1, v___f_1344_);
lean_ctor_set(v___x_1342_, 0, v___f_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___f_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___f_1344_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_firstTokens_1338_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1351_, lean_object* v_sep_1352_, uint8_t v_allowTrailingSep_1353_){
_start:
{
lean_object* v_info_1354_; lean_object* v_fn_1355_; lean_object* v_info_1356_; lean_object* v_fn_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1367_; 
v_info_1354_ = lean_ctor_get(v_p_1351_, 0);
lean_inc_ref(v_info_1354_);
v_fn_1355_ = lean_ctor_get(v_p_1351_, 1);
lean_inc_ref(v_fn_1355_);
lean_dec_ref(v_p_1351_);
v_info_1356_ = lean_ctor_get(v_sep_1352_, 0);
v_fn_1357_ = lean_ctor_get(v_sep_1352_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_sep_1352_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1359_ = v_sep_1352_;
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_fn_1357_);
lean_inc(v_info_1356_);
lean_dec(v_sep_1352_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1361_ = l_Lean_Parser_sepByInfo(v_info_1354_, v_info_1356_);
v___x_1362_ = lean_box(v_allowTrailingSep_1353_);
v___x_1363_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1363_, 0, v___x_1362_);
lean_closure_set(v___x_1363_, 1, v_fn_1355_);
lean_closure_set(v___x_1363_, 2, v_fn_1357_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1363_);
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1365_ = v___x_1359_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1368_, lean_object* v_sep_1369_, lean_object* v_allowTrailingSep_1370_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1371_; lean_object* v_res_1372_; 
v_allowTrailingSep_boxed_1371_ = lean_unbox(v_allowTrailingSep_1370_);
v_res_1372_ = l_Lean_Parser_sepByNoAntiquot(v_p_1368_, v_sep_1369_, v_allowTrailingSep_boxed_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1373_, lean_object* v_sep_1374_, uint8_t v_allowTrailingSep_1375_){
_start:
{
lean_object* v_info_1376_; lean_object* v_fn_1377_; lean_object* v_info_1378_; lean_object* v_fn_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1389_; 
v_info_1376_ = lean_ctor_get(v_p_1373_, 0);
lean_inc_ref(v_info_1376_);
v_fn_1377_ = lean_ctor_get(v_p_1373_, 1);
lean_inc_ref(v_fn_1377_);
lean_dec_ref(v_p_1373_);
v_info_1378_ = lean_ctor_get(v_sep_1374_, 0);
v_fn_1379_ = lean_ctor_get(v_sep_1374_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_sep_1374_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1381_ = v_sep_1374_;
v_isShared_1382_ = v_isSharedCheck_1389_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_fn_1379_);
lean_inc(v_info_1378_);
lean_dec(v_sep_1374_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1389_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1383_ = l_Lean_Parser_sepBy1Info(v_info_1376_, v_info_1378_);
v___x_1384_ = lean_box(v_allowTrailingSep_1375_);
v___x_1385_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1385_, 0, v___x_1384_);
lean_closure_set(v___x_1385_, 1, v_fn_1377_);
lean_closure_set(v___x_1385_, 2, v_fn_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1385_);
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1387_ = v___x_1381_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1390_, lean_object* v_sep_1391_, lean_object* v_allowTrailingSep_1392_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1393_; lean_object* v_res_1394_; 
v_allowTrailingSep_boxed_1393_ = lean_unbox(v_allowTrailingSep_1392_);
v_res_1394_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1390_, v_sep_1391_, v_allowTrailingSep_boxed_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1395_, lean_object* v_f_1396_, lean_object* v_c_1397_, lean_object* v_s_1398_){
_start:
{
lean_object* v_s_1399_; lean_object* v_stxStack_1400_; lean_object* v_errorMsg_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_s_1399_ = lean_apply_2(v_p_1395_, v_c_1397_, v_s_1398_);
v_stxStack_1400_ = lean_ctor_get(v_s_1399_, 0);
lean_inc_ref(v_stxStack_1400_);
v_errorMsg_1401_ = lean_ctor_get(v_s_1399_, 4);
lean_inc(v_errorMsg_1401_);
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1401_, v___x_1402_);
lean_dec(v_errorMsg_1401_);
if (v___x_1403_ == 0)
{
lean_dec_ref(v_stxStack_1400_);
lean_dec_ref(v_f_1396_);
return v_s_1399_;
}
else
{
lean_object* v_stx_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_stx_1404_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1400_);
lean_dec_ref(v_stxStack_1400_);
v___x_1405_ = l_Lean_Parser_ParserState_popSyntax(v_s_1399_);
v___x_1406_ = lean_apply_1(v_f_1396_, v_stx_1404_);
v___x_1407_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1405_, v___x_1406_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1408_){
_start:
{
lean_object* v_collectTokens_1409_; lean_object* v_collectKinds_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1418_; 
v_collectTokens_1409_ = lean_ctor_get(v_p_1408_, 0);
v_collectKinds_1410_ = lean_ctor_get(v_p_1408_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_p_1408_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v_p_1408_, 2);
lean_dec(v_unused_1419_);
v___x_1412_ = v_p_1408_;
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_collectKinds_1410_);
lean_inc(v_collectTokens_1409_);
lean_dec(v_p_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_box(1);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 2, v___x_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_collectTokens_1409_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_collectKinds_1410_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1420_, lean_object* v_f_1421_){
_start:
{
lean_object* v_info_1422_; lean_object* v_fn_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1432_; 
v_info_1422_ = lean_ctor_get(v_p_1420_, 0);
v_fn_1423_ = lean_ctor_get(v_p_1420_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_p_1420_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1425_ = v_p_1420_;
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_fn_1423_);
lean_inc(v_info_1422_);
lean_dec(v_p_1420_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = l_Lean_Parser_withResultOfInfo(v_info_1422_);
v___x_1428_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1428_, 0, v_fn_1423_);
lean_closure_set(v___x_1428_, 1, v_f_1421_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v___x_1428_);
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = l_Lean_Syntax_getNumArgs(v_stx_1433_);
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = lean_nat_dec_eq(v___x_1434_, v___x_1435_);
lean_dec(v___x_1434_);
if (v___x_1436_ == 0)
{
lean_inc(v_stx_1433_);
return v_stx_1433_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = l_Lean_Syntax_getArg(v_stx_1433_, v___x_1437_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1439_);
lean_dec(v_stx_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1442_){
_start:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___f_1443_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1444_ = l_Lean_Parser_many1NoAntiquot(v_p_1442_);
v___x_1445_ = l_Lean_Parser_withResultOf(v___x_1444_, v___f_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1446_, lean_object* v_errorMsg_1447_, lean_object* v_c_1448_, lean_object* v_s_1449_){
_start:
{
lean_object* v_pos_1450_; lean_object* v_toInputContext_1451_; uint8_t v___x_1452_; 
v_pos_1450_ = lean_ctor_get(v_s_1449_, 2);
v_toInputContext_1451_ = lean_ctor_get(v_c_1448_, 0);
v___x_1452_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1451_, v_pos_1450_);
if (v___x_1452_ == 0)
{
lean_object* v_inputString_1453_; uint32_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_inputString_1453_ = lean_ctor_get(v_toInputContext_1451_, 0);
v___x_1454_ = lean_string_utf8_get_fast(v_inputString_1453_, v_pos_1450_);
v___x_1455_ = lean_box_uint32(v___x_1454_);
v___x_1456_ = lean_apply_1(v_p_1446_, v___x_1455_);
v___x_1457_ = lean_unbox(v___x_1456_);
if (v___x_1457_ == 0)
{
uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = 1;
v___x_1459_ = lean_box(0);
v___x_1460_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1449_, v_errorMsg_1447_, v___x_1459_, v___x_1458_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; 
lean_inc(v_pos_1450_);
lean_dec_ref(v_errorMsg_1447_);
v___x_1461_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1449_, v_c_1448_, v_pos_1450_);
lean_dec(v_pos_1450_);
return v___x_1461_;
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_errorMsg_1447_);
lean_dec_ref(v_p_1446_);
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1449_, v___x_1462_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1464_, lean_object* v_errorMsg_1465_, lean_object* v_c_1466_, lean_object* v_s_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Parser_satisfyFn(v_p_1464_, v_errorMsg_1465_, v_c_1466_, v_s_1467_);
lean_dec_ref(v_c_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1469_, lean_object* v_c_1470_, lean_object* v_s_1471_){
_start:
{
lean_object* v_pos_1472_; lean_object* v_toInputContext_1473_; uint8_t v___x_1474_; 
v_pos_1472_ = lean_ctor_get(v_s_1471_, 2);
v_toInputContext_1473_ = lean_ctor_get(v_c_1470_, 0);
v___x_1474_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1473_, v_pos_1472_);
if (v___x_1474_ == 0)
{
lean_object* v_inputString_1475_; uint32_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_inputString_1475_ = lean_ctor_get(v_toInputContext_1473_, 0);
v___x_1476_ = lean_string_utf8_get_fast(v_inputString_1475_, v_pos_1472_);
v___x_1477_ = lean_box_uint32(v___x_1476_);
lean_inc_ref(v_p_1469_);
v___x_1478_ = lean_apply_1(v_p_1469_, v___x_1477_);
v___x_1479_ = lean_unbox(v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_pos_1472_);
v___x_1480_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1471_, v_c_1470_, v_pos_1472_);
lean_dec(v_pos_1472_);
v_s_1471_ = v___x_1480_;
goto _start;
}
else
{
lean_dec_ref(v_p_1469_);
return v_s_1471_;
}
}
else
{
lean_dec_ref(v_p_1469_);
return v_s_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1482_, lean_object* v_c_1483_, lean_object* v_s_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Parser_takeUntilFn(v_p_1482_, v_c_1483_, v_s_1484_);
lean_dec_ref(v_c_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1486_, uint32_t v_c_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1488_ = lean_box_uint32(v_c_1487_);
v___x_1489_ = lean_apply_1(v_p_1486_, v___x_1488_);
v___x_1490_ = lean_unbox(v___x_1489_);
if (v___x_1490_ == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = 1;
return v___x_1491_;
}
else
{
uint8_t v___x_1492_; 
v___x_1492_ = 0;
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1493_, lean_object* v_c_1494_){
_start:
{
uint32_t v_c_boxed_1495_; uint8_t v_res_1496_; lean_object* v_r_1497_; 
v_c_boxed_1495_ = lean_unbox_uint32(v_c_1494_);
lean_dec(v_c_1494_);
v_res_1496_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1493_, v_c_boxed_1495_);
v_r_1497_ = lean_box(v_res_1496_);
return v_r_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___f_1501_; lean_object* v___x_1502_; 
v___f_1501_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1501_, 0, v_p_1498_);
v___x_1502_ = l_Lean_Parser_takeUntilFn(v___f_1501_, v_a_1499_, v_a_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Parser_takeWhileFn(v_p_1503_, v_a_1504_, v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1507_, lean_object* v_errorMsg_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc_ref(v_p_1507_);
v___x_1511_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1511_, 0, v_p_1507_);
lean_closure_set(v___x_1511_, 1, v_errorMsg_1508_);
v___x_1512_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1512_, 0, v_p_1507_);
v___x_1513_ = l_Lean_Parser_andthenFn(v___x_1511_, v___x_1512_, v_a_1509_, v_a_1510_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1515_, lean_object* v_s_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1518_ = lean_box(0);
v___x_1519_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1516_, v___x_1517_, v___x_1518_, v_pushMissingOnError_1515_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1520_, lean_object* v_s_1521_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1522_; lean_object* v_res_1523_; 
v_pushMissingOnError_boxed_1522_ = lean_unbox(v_pushMissingOnError_1520_);
v_res_1523_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1522_, v_s_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1524_, lean_object* v_nesting_1525_, lean_object* v_c_1526_, lean_object* v_s_1527_){
_start:
{
lean_object* v_pos_1528_; lean_object* v_toInputContext_1529_; uint8_t v___x_1530_; 
v_pos_1528_ = lean_ctor_get(v_s_1527_, 2);
v_toInputContext_1529_ = lean_ctor_get(v_c_1526_, 0);
v___x_1530_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1529_, v_pos_1528_);
if (v___x_1530_ == 0)
{
lean_object* v_inputString_1531_; uint32_t v_curr_1532_; lean_object* v_i_1533_; uint32_t v___x_1534_; uint8_t v___x_1535_; 
v_inputString_1531_ = lean_ctor_get(v_toInputContext_1529_, 0);
v_curr_1532_ = lean_string_utf8_get_fast(v_inputString_1531_, v_pos_1528_);
v_i_1533_ = lean_string_utf8_next_fast(v_inputString_1531_, v_pos_1528_);
v___x_1534_ = 45;
v___x_1535_ = lean_uint32_dec_eq(v_curr_1532_, v___x_1534_);
if (v___x_1535_ == 0)
{
uint32_t v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = 47;
v___x_1537_ = lean_uint32_dec_eq(v_curr_1532_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Parser_ParserState_setPos(v_s_1527_, v_i_1533_);
v_s_1527_ = v___x_1538_;
goto _start;
}
else
{
uint8_t v___x_1540_; 
v___x_1540_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1529_, v_i_1533_);
if (v___x_1540_ == 0)
{
uint32_t v_curr_1541_; uint8_t v___x_1542_; 
v_curr_1541_ = lean_string_utf8_get_fast(v_inputString_1531_, v_i_1533_);
v___x_1542_ = lean_uint32_dec_eq(v_curr_1541_, v___x_1534_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Parser_ParserState_setPos(v_s_1527_, v_i_1533_);
v_s_1527_ = v___x_1543_;
goto _start;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_add(v_nesting_1525_, v___x_1545_);
lean_dec(v_nesting_1525_);
v___x_1547_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1527_, v_c_1526_, v_i_1533_);
v_nesting_1525_ = v___x_1546_;
v_s_1527_ = v___x_1547_;
goto _start;
}
}
else
{
lean_object* v___x_1549_; 
lean_dec(v_nesting_1525_);
v___x_1549_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1524_, v_s_1527_);
return v___x_1549_;
}
}
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1529_, v_i_1533_);
if (v___x_1550_ == 0)
{
uint32_t v_curr_1551_; uint32_t v___x_1552_; uint8_t v___x_1553_; 
v_curr_1551_ = lean_string_utf8_get_fast(v_inputString_1531_, v_i_1533_);
v___x_1552_ = 47;
v___x_1553_ = lean_uint32_dec_eq(v_curr_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Parser_ParserState_setPos(v_s_1527_, v_i_1533_);
v_s_1527_ = v___x_1554_;
goto _start;
}
else
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_dec_eq(v_nesting_1525_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_nat_sub(v_nesting_1525_, v___x_1556_);
lean_dec(v_nesting_1525_);
v___x_1559_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1527_, v_c_1526_, v_i_1533_);
v_nesting_1525_ = v___x_1558_;
v_s_1527_ = v___x_1559_;
goto _start;
}
else
{
lean_object* v___x_1561_; 
lean_dec(v_nesting_1525_);
v___x_1561_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1527_, v_c_1526_, v_i_1533_);
return v___x_1561_;
}
}
}
else
{
lean_object* v___x_1562_; 
lean_dec(v_nesting_1525_);
v___x_1562_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1524_, v_s_1527_);
return v___x_1562_;
}
}
}
else
{
lean_object* v___x_1563_; 
lean_dec(v_nesting_1525_);
v___x_1563_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1524_, v_s_1527_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1564_, lean_object* v_nesting_1565_, lean_object* v_c_1566_, lean_object* v_s_1567_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1568_; lean_object* v_res_1569_; 
v_pushMissingOnError_boxed_1568_ = lean_unbox(v_pushMissingOnError_1564_);
v_res_1569_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1568_, v_nesting_1565_, v_c_1566_, v_s_1567_);
lean_dec_ref(v_c_1566_);
return v_res_1569_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1570_){
_start:
{
uint32_t v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = 10;
v___x_1572_ = lean_uint32_dec_eq(v_c_1570_, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1573_){
_start:
{
uint32_t v_c_boxed_1574_; uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_c_boxed_1574_ = lean_unbox_uint32(v_c_1573_);
lean_dec(v_c_1573_);
v_res_1575_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1574_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1582_, lean_object* v_s_1583_){
_start:
{
lean_object* v_pos_1584_; lean_object* v_toInputContext_1588_; uint8_t v___x_1589_; 
v_pos_1584_ = lean_ctor_get(v_s_1583_, 2);
v_toInputContext_1588_ = lean_ctor_get(v_c_1582_, 0);
v___x_1589_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1588_, v_pos_1584_);
if (v___x_1589_ == 0)
{
lean_object* v_inputString_1590_; uint32_t v_curr_1591_; uint32_t v___x_1592_; uint8_t v___x_1593_; 
v_inputString_1590_ = lean_ctor_get(v_toInputContext_1588_, 0);
v_curr_1591_ = lean_string_utf8_get_fast(v_inputString_1590_, v_pos_1584_);
v___x_1592_ = 9;
v___x_1593_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
uint32_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = 13;
v___x_1595_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1594_);
if (v___x_1595_ == 0)
{
uint8_t v___y_1597_; uint8_t v___y_1624_; uint32_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = 32;
v___x_1628_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1627_);
if (v___x_1628_ == 0)
{
v___y_1624_ = v___x_1593_;
goto v___jp_1623_;
}
else
{
v___y_1624_ = v___x_1628_;
goto v___jp_1623_;
}
v___jp_1596_:
{
if (v___y_1597_ == 0)
{
uint32_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = 45;
v___x_1599_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1598_);
if (v___x_1599_ == 0)
{
uint32_t v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = 47;
v___x_1601_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_dec_ref(v_c_1582_);
return v_s_1583_;
}
else
{
lean_object* v_i_1602_; uint32_t v_curr_1603_; uint8_t v___x_1604_; 
v_i_1602_ = lean_string_utf8_next_fast(v_inputString_1590_, v_pos_1584_);
v_curr_1603_ = lean_string_utf8_get(v_inputString_1590_, v_i_1602_);
v___x_1604_ = lean_uint32_dec_eq(v_curr_1603_, v___x_1598_);
if (v___x_1604_ == 0)
{
lean_dec_ref(v_c_1582_);
return v_s_1583_;
}
else
{
lean_object* v_i_1605_; uint32_t v_curr_1606_; uint8_t v___x_1607_; 
v_i_1605_ = lean_string_utf8_next(v_inputString_1590_, v_i_1602_);
v_curr_1606_ = lean_string_utf8_get(v_inputString_1590_, v_i_1605_);
v___x_1607_ = lean_uint32_dec_eq(v_curr_1606_, v___x_1598_);
if (v___x_1607_ == 0)
{
uint32_t v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = 33;
v___x_1609_ = lean_uint32_dec_eq(v_curr_1606_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_box(v___x_1609_);
v___x_1612_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1612_, 0, v___x_1611_);
lean_closure_set(v___x_1612_, 1, v___x_1610_);
v___x_1613_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1614_ = l_Lean_Parser_ParserState_next(v_s_1583_, v_c_1582_, v_i_1605_);
lean_dec(v_i_1605_);
v___x_1615_ = l_Lean_Parser_andthenFn(v___x_1612_, v___x_1613_, v_c_1582_, v___x_1614_);
return v___x_1615_;
}
else
{
lean_dec(v_i_1605_);
lean_dec_ref(v_c_1582_);
return v_s_1583_;
}
}
else
{
lean_dec(v_i_1605_);
lean_dec_ref(v_c_1582_);
return v_s_1583_;
}
}
}
}
else
{
lean_object* v_i_1616_; uint32_t v_curr_1617_; uint8_t v___x_1618_; 
v_i_1616_ = lean_string_utf8_next_fast(v_inputString_1590_, v_pos_1584_);
v_curr_1617_ = lean_string_utf8_get(v_inputString_1590_, v_i_1616_);
v___x_1618_ = lean_uint32_dec_eq(v_curr_1617_, v___x_1598_);
if (v___x_1618_ == 0)
{
lean_dec_ref(v_c_1582_);
return v_s_1583_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1619_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1620_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1621_ = l_Lean_Parser_ParserState_next(v_s_1583_, v_c_1582_, v_i_1616_);
v___x_1622_ = l_Lean_Parser_andthenFn(v___x_1619_, v___x_1620_, v_c_1582_, v___x_1621_);
return v___x_1622_;
}
}
}
else
{
lean_inc(v_pos_1584_);
goto v___jp_1585_;
}
}
v___jp_1623_:
{
if (v___y_1624_ == 0)
{
if (v___x_1595_ == 0)
{
uint32_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = 10;
v___x_1626_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1625_);
v___y_1597_ = v___x_1626_;
goto v___jp_1596_;
}
else
{
v___y_1597_ = v___x_1595_;
goto v___jp_1596_;
}
}
else
{
lean_inc(v_pos_1584_);
goto v___jp_1585_;
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref(v_c_1582_);
v___x_1629_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1630_ = lean_box(0);
v___x_1631_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1583_, v___x_1629_, v___x_1630_, v___x_1593_);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v_c_1582_);
v___x_1632_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1633_ = lean_box(0);
v___x_1634_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1583_, v___x_1632_, v___x_1633_, v___x_1589_);
return v___x_1634_;
}
}
else
{
lean_dec_ref(v_c_1582_);
return v_s_1583_;
}
v___jp_1585_:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1583_, v_c_1582_, v_pos_1584_);
lean_dec(v_pos_1584_);
v_s_1583_ = v___x_1586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1635_, lean_object* v_p_1636_){
_start:
{
lean_object* v_toInputContext_1637_; lean_object* v_inputString_1638_; lean_object* v_endPos_1639_; uint8_t v___x_1640_; 
v_toInputContext_1637_ = lean_ctor_get(v_c_1635_, 0);
v_inputString_1638_ = lean_ctor_get(v_toInputContext_1637_, 0);
v_endPos_1639_ = lean_ctor_get(v_toInputContext_1637_, 3);
v___x_1640_ = lean_nat_dec_le(v_p_1636_, v_endPos_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_inc(v_endPos_1639_);
lean_inc_ref(v_inputString_1638_);
v___x_1641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1641_, 0, v_inputString_1638_);
lean_ctor_set(v___x_1641_, 1, v_p_1636_);
lean_ctor_set(v___x_1641_, 2, v_endPos_1639_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
lean_inc(v_p_1636_);
lean_inc_ref(v_inputString_1638_);
v___x_1642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1642_, 0, v_inputString_1638_);
lean_ctor_set(v___x_1642_, 1, v_p_1636_);
lean_ctor_set(v___x_1642_, 2, v_p_1636_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1643_, lean_object* v_p_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1643_, v_p_1644_);
lean_dec_ref(v_c_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1646_, uint8_t v_trailingWs_1647_, lean_object* v_c_1648_, lean_object* v_s_1649_){
_start:
{
lean_object* v_toInputContext_1650_; lean_object* v_pos_1651_; lean_object* v_inputString_1652_; lean_object* v_endPos_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1681_; 
v_toInputContext_1650_ = lean_ctor_get(v_c_1648_, 0);
lean_inc_ref(v_toInputContext_1650_);
v_pos_1651_ = lean_ctor_get(v_s_1649_, 2);
v_inputString_1652_ = lean_ctor_get(v_toInputContext_1650_, 0);
v_endPos_1653_ = lean_ctor_get(v_toInputContext_1650_, 3);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_toInputContext_1650_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1682_ = lean_ctor_get(v_toInputContext_1650_, 2);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_toInputContext_1650_, 1);
lean_dec(v_unused_1683_);
v___x_1655_ = v_toInputContext_1650_;
v_isShared_1656_ = v_isSharedCheck_1681_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_endPos_1653_);
lean_inc(v_inputString_1652_);
lean_dec(v_toInputContext_1650_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1681_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_leading_1657_; lean_object* v_val_1658_; 
lean_inc(v_startPos_1646_);
v_leading_1657_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1648_, v_startPos_1646_);
v_val_1658_ = lean_string_utf8_extract(v_inputString_1652_, v_startPos_1646_, v_pos_1651_);
if (v_trailingWs_1647_ == 0)
{
lean_object* v_trailing_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_endPos_1653_);
lean_dec_ref(v_inputString_1652_);
lean_inc(v_pos_1651_);
v_trailing_1659_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1648_, v_pos_1651_);
lean_dec_ref(v_c_1648_);
v___x_1660_ = lean_string_utf8_byte_size(v_val_1658_);
v___x_1661_ = lean_nat_add(v_startPos_1646_, v___x_1660_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v___x_1661_);
lean_ctor_set(v___x_1655_, 2, v_trailing_1659_);
lean_ctor_set(v___x_1655_, 1, v_startPos_1646_);
lean_ctor_set(v___x_1655_, 0, v_leading_1657_);
v___x_1663_ = v___x_1655_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_leading_1657_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_startPos_1646_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_trailing_1659_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v_atom_1664_; lean_object* v___x_1665_; 
v_atom_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1664_, 0, v___x_1663_);
lean_ctor_set(v_atom_1664_, 1, v_val_1658_);
v___x_1665_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1649_, v_atom_1664_);
return v___x_1665_;
}
}
else
{
lean_object* v_s_1667_; lean_object* v___y_1669_; lean_object* v_pos_1677_; uint8_t v___x_1678_; 
lean_inc(v_pos_1651_);
v_s_1667_ = l_Lean_Parser_whitespace(v_c_1648_, v_s_1649_);
v_pos_1677_ = lean_ctor_get(v_s_1667_, 2);
lean_inc(v_pos_1677_);
v___x_1678_ = lean_nat_dec_le(v_pos_1677_, v_endPos_1653_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_pos_1677_);
v___x_1679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1679_, 0, v_inputString_1652_);
lean_ctor_set(v___x_1679_, 1, v_pos_1651_);
lean_ctor_set(v___x_1679_, 2, v_endPos_1653_);
v___y_1669_ = v___x_1679_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1680_; 
lean_dec(v_endPos_1653_);
v___x_1680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1680_, 0, v_inputString_1652_);
lean_ctor_set(v___x_1680_, 1, v_pos_1651_);
lean_ctor_set(v___x_1680_, 2, v_pos_1677_);
v___y_1669_ = v___x_1680_;
goto v___jp_1668_;
}
v___jp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1670_ = lean_string_utf8_byte_size(v_val_1658_);
v___x_1671_ = lean_nat_add(v_startPos_1646_, v___x_1670_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v___x_1671_);
lean_ctor_set(v___x_1655_, 2, v___y_1669_);
lean_ctor_set(v___x_1655_, 1, v_startPos_1646_);
lean_ctor_set(v___x_1655_, 0, v_leading_1657_);
v___x_1673_ = v___x_1655_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_leading_1657_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_startPos_1646_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v___y_1669_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v_atom_1674_; lean_object* v___x_1675_; 
v_atom_1674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1674_, 0, v___x_1673_);
lean_ctor_set(v_atom_1674_, 1, v_val_1658_);
v___x_1675_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1667_, v_atom_1674_);
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1684_, lean_object* v_trailingWs_1685_, lean_object* v_c_1686_, lean_object* v_s_1687_){
_start:
{
uint8_t v_trailingWs_boxed_1688_; lean_object* v_res_1689_; 
v_trailingWs_boxed_1688_ = lean_unbox(v_trailingWs_1685_);
v_res_1689_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1684_, v_trailingWs_boxed_1688_, v_c_1686_, v_s_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1690_, uint8_t v_trailingWs_1691_, lean_object* v_c_1692_, lean_object* v_s_1693_){
_start:
{
lean_object* v_pos_1694_; lean_object* v_s_1695_; lean_object* v_errorMsg_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v_pos_1694_ = lean_ctor_get(v_s_1693_, 2);
lean_inc(v_pos_1694_);
lean_inc_ref(v_c_1692_);
v_s_1695_ = lean_apply_2(v_p_1690_, v_c_1692_, v_s_1693_);
v_errorMsg_1696_ = lean_ctor_get(v_s_1695_, 4);
lean_inc(v_errorMsg_1696_);
v___x_1697_ = lean_box(0);
v___x_1698_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1696_, v___x_1697_);
lean_dec(v_errorMsg_1696_);
if (v___x_1698_ == 0)
{
lean_dec(v_pos_1694_);
lean_dec_ref(v_c_1692_);
return v_s_1695_;
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1694_, v_trailingWs_1691_, v_c_1692_, v_s_1695_);
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1700_, lean_object* v_trailingWs_1701_, lean_object* v_c_1702_, lean_object* v_s_1703_){
_start:
{
uint8_t v_trailingWs_boxed_1704_; lean_object* v_res_1705_; 
v_trailingWs_boxed_1704_ = lean_unbox(v_trailingWs_1701_);
v_res_1705_ = l_Lean_Parser_rawFn(v_p_1700_, v_trailingWs_boxed_1704_, v_c_1702_, v_s_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1706_, uint32_t v_d_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_uint32_dec_eq(v_c_1706_, v_d_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1709_, lean_object* v_d_1710_){
_start:
{
uint32_t v_c_boxed_1711_; uint32_t v_d_boxed_1712_; uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_c_boxed_1711_ = lean_unbox_uint32(v_c_1709_);
lean_dec(v_c_1709_);
v_d_boxed_1712_ = lean_unbox_uint32(v_d_1710_);
lean_dec(v_d_1710_);
v_res_1713_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1711_, v_d_boxed_1712_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1717_, uint8_t v_trailingWs_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1721_ = lean_box_uint32(v_c_1717_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1722_, 0, v___x_1721_);
v___x_1723_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1724_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1725_ = lean_string_push(v___x_1724_, v_c_1717_);
v___x_1726_ = lean_string_append(v___x_1723_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = lean_string_append(v___x_1726_, v___x_1723_);
v___x_1728_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1728_, 0, v___f_1722_);
lean_closure_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_Parser_rawFn(v___x_1728_, v_trailingWs_1718_, v_a_1719_, v_a_1720_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1730_, lean_object* v_trailingWs_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
uint32_t v_c_boxed_1734_; uint8_t v_trailingWs_boxed_1735_; lean_object* v_res_1736_; 
v_c_boxed_1734_ = lean_unbox_uint32(v_c_1730_);
lean_dec(v_c_1730_);
v_trailingWs_boxed_1735_ = lean_unbox(v_trailingWs_1731_);
v_res_1736_ = l_Lean_Parser_chFn(v_c_boxed_1734_, v_trailingWs_boxed_1735_, v_a_1732_, v_a_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1737_, uint8_t v_trailingWs_1738_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1739_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1740_ = lean_box_uint32(v_c_1737_);
v___x_1741_ = lean_box(v_trailingWs_1738_);
v___x_1742_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1742_, 0, v___x_1740_);
lean_closure_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1739_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1744_, lean_object* v_trailingWs_1745_){
_start:
{
uint32_t v_c_boxed_1746_; uint8_t v_trailingWs_boxed_1747_; lean_object* v_res_1748_; 
v_c_boxed_1746_ = lean_unbox_uint32(v_c_1744_);
lean_dec(v_c_1744_);
v_trailingWs_boxed_1747_ = lean_unbox(v_trailingWs_1745_);
v_res_1748_ = l_Lean_Parser_rawCh(v_c_boxed_1746_, v_trailingWs_boxed_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1750_, lean_object* v_s_1751_){
_start:
{
lean_object* v_pos_1752_; lean_object* v_toInputContext_1753_; uint8_t v___x_1754_; 
v_pos_1752_ = lean_ctor_get(v_s_1751_, 2);
v_toInputContext_1753_ = lean_ctor_get(v_c_1750_, 0);
v___x_1754_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1753_, v_pos_1752_);
if (v___x_1754_ == 0)
{
lean_object* v_inputString_1755_; uint8_t v___x_1756_; uint32_t v_curr_1757_; lean_object* v_i_1758_; uint8_t v___y_1760_; uint8_t v___y_1766_; uint8_t v___y_1773_; uint32_t v___x_1779_; uint8_t v___x_1780_; 
v_inputString_1755_ = lean_ctor_get(v_toInputContext_1753_, 0);
v___x_1756_ = 1;
v_curr_1757_ = lean_string_utf8_get_fast(v_inputString_1755_, v_pos_1752_);
v_i_1758_ = lean_string_utf8_next_fast(v_inputString_1755_, v_pos_1752_);
v___x_1779_ = 48;
v___x_1780_ = lean_uint32_dec_le(v___x_1779_, v_curr_1757_);
if (v___x_1780_ == 0)
{
v___y_1773_ = v___x_1780_;
goto v___jp_1772_;
}
else
{
uint32_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 57;
v___x_1782_ = lean_uint32_dec_le(v_curr_1757_, v___x_1781_);
v___y_1773_ = v___x_1782_;
goto v___jp_1772_;
}
v___jp_1759_:
{
if (v___y_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1762_ = lean_box(0);
v___x_1763_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1751_, v___x_1761_, v___x_1762_, v___x_1756_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Parser_ParserState_setPos(v_s_1751_, v_i_1758_);
return v___x_1764_;
}
}
v___jp_1765_:
{
if (v___y_1766_ == 0)
{
uint32_t v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = 65;
v___x_1768_ = lean_uint32_dec_le(v___x_1767_, v_curr_1757_);
if (v___x_1768_ == 0)
{
v___y_1760_ = v___x_1768_;
goto v___jp_1759_;
}
else
{
uint32_t v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = 70;
v___x_1770_ = lean_uint32_dec_le(v_curr_1757_, v___x_1769_);
v___y_1760_ = v___x_1770_;
goto v___jp_1759_;
}
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Parser_ParserState_setPos(v_s_1751_, v_i_1758_);
return v___x_1771_;
}
}
v___jp_1772_:
{
if (v___y_1773_ == 0)
{
uint32_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = 97;
v___x_1775_ = lean_uint32_dec_le(v___x_1774_, v_curr_1757_);
if (v___x_1775_ == 0)
{
v___y_1766_ = v___x_1775_;
goto v___jp_1765_;
}
else
{
uint32_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = 102;
v___x_1777_ = lean_uint32_dec_le(v_curr_1757_, v___x_1776_);
v___y_1766_ = v___x_1777_;
goto v___jp_1765_;
}
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Parser_ParserState_setPos(v_s_1751_, v_i_1758_);
return v___x_1778_;
}
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1751_, v___x_1783_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1785_, lean_object* v_s_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Parser_hexDigitFn(v_c_1785_, v_s_1786_);
lean_dec_ref(v_c_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1790_, lean_object* v_c_1791_, lean_object* v_s_1792_){
_start:
{
lean_object* v_pos_1793_; lean_object* v_toInputContext_1797_; uint8_t v___x_1798_; 
v_pos_1793_ = lean_ctor_get(v_s_1792_, 2);
v_toInputContext_1797_ = lean_ctor_get(v_c_1791_, 0);
v___x_1798_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1797_, v_pos_1793_);
if (v___x_1798_ == 0)
{
lean_object* v_inputString_1799_; uint8_t v___x_1800_; uint8_t v___y_1802_; uint32_t v_curr_1806_; uint8_t v___y_1808_; uint32_t v___x_1813_; uint8_t v___x_1814_; 
v_inputString_1799_ = lean_ctor_get(v_toInputContext_1797_, 0);
v___x_1800_ = 1;
v_curr_1806_ = lean_string_utf8_get_fast(v_inputString_1799_, v_pos_1793_);
v___x_1813_ = 10;
v___x_1814_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint32_t v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = 32;
v___x_1816_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1815_);
if (v___x_1816_ == 0)
{
uint32_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = 9;
v___x_1818_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1817_);
v___y_1808_ = v___x_1818_;
goto v___jp_1807_;
}
else
{
v___y_1808_ = v___x_1816_;
goto v___jp_1807_;
}
}
else
{
if (v_seenNewline_1790_ == 0)
{
lean_object* v___x_1819_; 
lean_inc(v_pos_1793_);
v___x_1819_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1792_, v_c_1791_, v_pos_1793_);
lean_dec(v_pos_1793_);
v_seenNewline_1790_ = v___x_1800_;
v_s_1792_ = v___x_1819_;
goto _start;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1822_ = lean_box(0);
v___x_1823_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1792_, v___x_1821_, v___x_1822_, v___x_1800_);
return v___x_1823_;
}
}
v___jp_1801_:
{
if (v___y_1802_ == 0)
{
if (v_seenNewline_1790_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1804_ = lean_box(0);
v___x_1805_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1792_, v___x_1803_, v___x_1804_, v___x_1800_);
return v___x_1805_;
}
else
{
return v_s_1792_;
}
}
else
{
lean_inc(v_pos_1793_);
goto v___jp_1794_;
}
}
v___jp_1807_:
{
if (v___y_1808_ == 0)
{
uint32_t v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = 13;
v___x_1810_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1809_);
if (v___x_1810_ == 0)
{
uint32_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = 10;
v___x_1812_ = lean_uint32_dec_eq(v_curr_1806_, v___x_1811_);
v___y_1802_ = v___x_1812_;
goto v___jp_1801_;
}
else
{
v___y_1802_ = v___x_1810_;
goto v___jp_1801_;
}
}
else
{
lean_inc(v_pos_1793_);
goto v___jp_1794_;
}
}
}
else
{
return v_s_1792_;
}
v___jp_1794_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1792_, v_c_1791_, v_pos_1793_);
lean_dec(v_pos_1793_);
v_s_1792_ = v___x_1795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1824_, lean_object* v_c_1825_, lean_object* v_s_1826_){
_start:
{
uint8_t v_seenNewline_boxed_1827_; lean_object* v_res_1828_; 
v_seenNewline_boxed_1827_ = lean_unbox(v_seenNewline_1824_);
v_res_1828_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1827_, v_c_1825_, v_s_1826_);
lean_dec_ref(v_c_1825_);
return v_res_1828_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1830_);
v___x_1831_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1831_, 0, v___x_1830_);
lean_closure_set(v___x_1831_, 1, v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1833_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1834_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1834_, 0, v___x_1833_);
lean_closure_set(v___x_1834_, 1, v___x_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1835_, uint8_t v_inString_1836_, lean_object* v_c_1837_, lean_object* v_s_1838_){
_start:
{
lean_object* v_pos_1839_; lean_object* v_toInputContext_1840_; uint8_t v___x_1841_; 
v_pos_1839_ = lean_ctor_get(v_s_1838_, 2);
v_toInputContext_1840_ = lean_ctor_get(v_c_1837_, 0);
v___x_1841_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1840_, v_pos_1839_);
if (v___x_1841_ == 0)
{
lean_object* v_inputString_1842_; uint32_t v_curr_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_inputString_1842_ = lean_ctor_get(v_toInputContext_1840_, 0);
v_curr_1843_ = lean_string_utf8_get_fast(v_inputString_1842_, v_pos_1839_);
v___x_1844_ = lean_box_uint32(v_curr_1843_);
v___x_1845_ = lean_apply_1(v_isQuotable_1835_, v___x_1844_);
v___x_1846_ = lean_unbox(v___x_1845_);
if (v___x_1846_ == 0)
{
uint32_t v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = 120;
v___x_1848_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1847_);
if (v___x_1848_ == 0)
{
uint32_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = 117;
v___x_1850_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1849_);
if (v___x_1850_ == 0)
{
uint8_t v___x_1851_; 
v___x_1851_ = 1;
if (v_inString_1836_ == 0)
{
lean_dec_ref(v_c_1837_);
goto v___jp_1852_;
}
else
{
uint32_t v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = 10;
v___x_1857_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_c_1837_);
goto v___jp_1852_;
}
else
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Parser_stringGapFn(v___x_1850_, v_c_1837_, v_s_1838_);
lean_dec_ref(v_c_1837_);
return v___x_1858_;
}
}
v___jp_1852_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1854_ = lean_box(0);
v___x_1855_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1838_, v___x_1853_, v___x_1854_, v___x_1851_);
return v___x_1855_;
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_inc(v_pos_1839_);
v___x_1859_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1860_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1861_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1838_, v_c_1837_, v_pos_1839_);
lean_dec(v_pos_1839_);
v___x_1862_ = l_Lean_Parser_andthenFn(v___x_1859_, v___x_1860_, v_c_1837_, v___x_1861_);
return v___x_1862_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_inc(v_pos_1839_);
v___x_1863_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1864_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1838_, v_c_1837_, v_pos_1839_);
lean_dec(v_pos_1839_);
lean_inc_ref(v___x_1863_);
v___x_1865_ = l_Lean_Parser_andthenFn(v___x_1863_, v___x_1863_, v_c_1837_, v___x_1864_);
return v___x_1865_;
}
}
else
{
lean_object* v___x_1866_; 
lean_inc(v_pos_1839_);
v___x_1866_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1838_, v_c_1837_, v_pos_1839_);
lean_dec(v_pos_1839_);
lean_dec_ref(v_c_1837_);
return v___x_1866_;
}
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec_ref(v_c_1837_);
lean_dec_ref(v_isQuotable_1835_);
v___x_1867_ = lean_box(0);
v___x_1868_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1838_, v___x_1867_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1869_, lean_object* v_inString_1870_, lean_object* v_c_1871_, lean_object* v_s_1872_){
_start:
{
uint8_t v_inString_boxed_1873_; lean_object* v_res_1874_; 
v_inString_boxed_1873_ = lean_unbox(v_inString_1870_);
v_res_1874_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1869_, v_inString_boxed_1873_, v_c_1871_, v_s_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1875_){
_start:
{
uint8_t v___y_1877_; uint32_t v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = 92;
v___x_1887_ = lean_uint32_dec_eq(v_c_1875_, v___x_1886_);
if (v___x_1887_ == 0)
{
uint32_t v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = 34;
v___x_1889_ = lean_uint32_dec_eq(v_c_1875_, v___x_1888_);
v___y_1877_ = v___x_1889_;
goto v___jp_1876_;
}
else
{
v___y_1877_ = v___x_1887_;
goto v___jp_1876_;
}
v___jp_1876_:
{
if (v___y_1877_ == 0)
{
uint32_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = 39;
v___x_1879_ = lean_uint32_dec_eq(v_c_1875_, v___x_1878_);
if (v___x_1879_ == 0)
{
uint32_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = 114;
v___x_1881_ = lean_uint32_dec_eq(v_c_1875_, v___x_1880_);
if (v___x_1881_ == 0)
{
uint32_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = 110;
v___x_1883_ = lean_uint32_dec_eq(v_c_1875_, v___x_1882_);
if (v___x_1883_ == 0)
{
uint32_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = 116;
v___x_1885_ = lean_uint32_dec_eq(v_c_1875_, v___x_1884_);
return v___x_1885_;
}
else
{
return v___x_1883_;
}
}
else
{
return v___x_1881_;
}
}
else
{
return v___x_1879_;
}
}
else
{
return v___y_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1890_){
_start:
{
uint32_t v_c_boxed_1891_; uint8_t v_res_1892_; lean_object* v_r_1893_; 
v_c_boxed_1891_ = lean_unbox_uint32(v_c_1890_);
lean_dec(v_c_1890_);
v_res_1892_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1891_);
v_r_1893_ = lean_box(v_res_1892_);
return v_r_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1898_ = 0;
v___x_1899_ = l_Lean_Parser_quotedCharCoreFn(v___x_1897_, v___x_1898_, v_a_1895_, v_a_1896_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1903_ = 1;
v___x_1904_ = l_Lean_Parser_quotedCharCoreFn(v___x_1902_, v___x_1903_, v_a_1900_, v_a_1901_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1905_, lean_object* v_startPos_1906_, uint8_t v_includeWhitespace_1907_, lean_object* v_c_1908_, lean_object* v_s_1909_){
_start:
{
lean_object* v_pos_1910_; lean_object* v_errorMsg_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_pos_1910_ = lean_ctor_get(v_s_1909_, 2);
v_errorMsg_1911_ = lean_ctor_get(v_s_1909_, 4);
v___x_1912_ = lean_box(0);
v___x_1913_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_dec_ref(v_c_1908_);
lean_dec(v_startPos_1906_);
lean_dec(v_n_1905_);
return v_s_1909_;
}
else
{
lean_object* v_toInputContext_1914_; lean_object* v_inputString_1915_; lean_object* v_endPos_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1938_; 
lean_inc(v_pos_1910_);
v_toInputContext_1914_ = lean_ctor_get(v_c_1908_, 0);
lean_inc_ref(v_toInputContext_1914_);
v_inputString_1915_ = lean_ctor_get(v_toInputContext_1914_, 0);
v_endPos_1916_ = lean_ctor_get(v_toInputContext_1914_, 3);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_toInputContext_1914_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; lean_object* v_unused_1940_; 
v_unused_1939_ = lean_ctor_get(v_toInputContext_1914_, 2);
lean_dec(v_unused_1939_);
v_unused_1940_ = lean_ctor_get(v_toInputContext_1914_, 1);
lean_dec(v_unused_1940_);
v___x_1918_ = v_toInputContext_1914_;
v_isShared_1919_ = v_isSharedCheck_1938_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_endPos_1916_);
lean_inc(v_inputString_1915_);
lean_dec(v_toInputContext_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1938_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_leading_1920_; lean_object* v_val_1921_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1931_; lean_object* v_pos_1932_; 
lean_inc(v_startPos_1906_);
v_leading_1920_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1908_, v_startPos_1906_);
v_val_1921_ = lean_string_utf8_extract(v_inputString_1915_, v_startPos_1906_, v_pos_1910_);
if (v_includeWhitespace_1907_ == 0)
{
lean_dec_ref(v_c_1908_);
lean_inc(v_pos_1910_);
v___y_1931_ = v_s_1909_;
v_pos_1932_ = v_pos_1910_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1936_; lean_object* v_pos_1937_; 
v___x_1936_ = l_Lean_Parser_whitespace(v_c_1908_, v_s_1909_);
v_pos_1937_ = lean_ctor_get(v___x_1936_, 2);
lean_inc(v_pos_1937_);
v___y_1931_ = v___x_1936_;
v_pos_1932_ = v_pos_1937_;
goto v___jp_1930_;
}
v___jp_1922_:
{
lean_object* v_info_1926_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 3, v_pos_1910_);
lean_ctor_set(v___x_1918_, 2, v___y_1924_);
lean_ctor_set(v___x_1918_, 1, v_startPos_1906_);
lean_ctor_set(v___x_1918_, 0, v_leading_1920_);
v_info_1926_ = v___x_1918_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_leading_1920_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_startPos_1906_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v___y_1924_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_pos_1910_);
v_info_1926_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = l_Lean_Syntax_mkLit(v_n_1905_, v_val_1921_, v_info_1926_);
v___x_1928_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1923_, v___x_1927_);
return v___x_1928_;
}
}
v___jp_1930_:
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_nat_dec_le(v_pos_1932_, v_endPos_1916_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec(v_pos_1932_);
lean_inc(v_pos_1910_);
v___x_1934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1934_, 0, v_inputString_1915_);
lean_ctor_set(v___x_1934_, 1, v_pos_1910_);
lean_ctor_set(v___x_1934_, 2, v_endPos_1916_);
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___x_1934_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1935_; 
lean_dec(v_endPos_1916_);
lean_inc(v_pos_1910_);
v___x_1935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1935_, 0, v_inputString_1915_);
lean_ctor_set(v___x_1935_, 1, v_pos_1910_);
lean_ctor_set(v___x_1935_, 2, v_pos_1932_);
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___x_1935_;
goto v___jp_1922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1941_, lean_object* v_startPos_1942_, lean_object* v_includeWhitespace_1943_, lean_object* v_c_1944_, lean_object* v_s_1945_){
_start:
{
uint8_t v_includeWhitespace_boxed_1946_; lean_object* v_res_1947_; 
v_includeWhitespace_boxed_1946_ = lean_unbox(v_includeWhitespace_1943_);
v_res_1947_ = l_Lean_Parser_mkNodeToken(v_n_1941_, v_startPos_1942_, v_includeWhitespace_boxed_1946_, v_c_1944_, v_s_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1952_, lean_object* v_c_1953_, lean_object* v_s_1954_){
_start:
{
lean_object* v_pos_1955_; lean_object* v_toInputContext_1956_; uint8_t v___x_1957_; 
v_pos_1955_ = lean_ctor_get(v_s_1954_, 2);
v_toInputContext_1956_ = lean_ctor_get(v_c_1953_, 0);
v___x_1957_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1956_, v_pos_1955_);
if (v___x_1957_ == 0)
{
lean_object* v_inputString_1958_; uint8_t v___x_1959_; lean_object* v___y_1961_; uint32_t v_curr_1976_; lean_object* v___x_1977_; lean_object* v_s_1978_; uint32_t v___x_1979_; uint8_t v___x_1980_; 
v_inputString_1958_ = lean_ctor_get(v_toInputContext_1956_, 0);
v___x_1959_ = 1;
v_curr_1976_ = lean_string_utf8_get_fast(v_inputString_1958_, v_pos_1955_);
v___x_1977_ = lean_string_utf8_next_fast(v_inputString_1958_, v_pos_1955_);
v_s_1978_ = l_Lean_Parser_ParserState_setPos(v_s_1954_, v___x_1977_);
v___x_1979_ = 92;
v___x_1980_ = lean_uint32_dec_eq(v_curr_1976_, v___x_1979_);
if (v___x_1980_ == 0)
{
v___y_1961_ = v_s_1978_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1981_; 
lean_inc_ref(v_c_1953_);
v___x_1981_ = l_Lean_Parser_quotedCharFn(v_c_1953_, v_s_1978_);
v___y_1961_ = v___x_1981_;
goto v___jp_1960_;
}
v___jp_1960_:
{
lean_object* v_pos_1962_; lean_object* v_errorMsg_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_pos_1962_ = lean_ctor_get(v___y_1961_, 2);
v_errorMsg_1963_ = lean_ctor_get(v___y_1961_, 4);
v___x_1964_ = lean_box(0);
v___x_1965_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v_c_1953_);
lean_dec(v_startPos_1952_);
return v___y_1961_;
}
else
{
if (v___x_1957_ == 0)
{
uint32_t v_curr_1966_; lean_object* v___x_1967_; lean_object* v_s_1968_; uint32_t v___x_1969_; uint8_t v___x_1970_; 
v_curr_1966_ = lean_string_utf8_get(v_inputString_1958_, v_pos_1962_);
v___x_1967_ = lean_string_utf8_next(v_inputString_1958_, v_pos_1962_);
v_s_1968_ = l_Lean_Parser_ParserState_setPos(v___y_1961_, v___x_1967_);
v___x_1969_ = 39;
v___x_1970_ = lean_uint32_dec_eq(v_curr_1966_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v_c_1953_);
lean_dec(v_startPos_1952_);
v___x_1971_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1972_ = lean_box(0);
v___x_1973_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1968_, v___x_1971_, v___x_1972_, v___x_1959_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1975_ = l_Lean_Parser_mkNodeToken(v___x_1974_, v_startPos_1952_, v___x_1959_, v_c_1953_, v_s_1968_);
return v___x_1975_;
}
}
else
{
lean_dec_ref(v_c_1953_);
lean_dec(v_startPos_1952_);
return v___y_1961_;
}
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_c_1953_);
lean_dec(v_startPos_1952_);
v___x_1982_ = lean_box(0);
v___x_1983_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1954_, v___x_1982_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_1988_, lean_object* v_includeWhitespace_1989_, lean_object* v_c_1990_, lean_object* v_s_1991_){
_start:
{
uint8_t v_includeWhitespace_boxed_1992_; lean_object* v_res_1993_; 
v_includeWhitespace_boxed_1992_ = lean_unbox(v_includeWhitespace_1989_);
v_res_1993_ = l_Lean_Parser_strLitFnAux(v_startPos_1988_, v_includeWhitespace_boxed_1992_, v_c_1990_, v_s_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_1994_, uint8_t v_includeWhitespace_1995_, lean_object* v_c_1996_, lean_object* v_s_1997_){
_start:
{
lean_object* v_pos_1998_; lean_object* v_toInputContext_1999_; uint8_t v___x_2000_; 
v_pos_1998_ = lean_ctor_get(v_s_1997_, 2);
v_toInputContext_1999_ = lean_ctor_get(v_c_1996_, 0);
v___x_2000_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1999_, v_pos_1998_);
if (v___x_2000_ == 0)
{
lean_object* v_inputString_2001_; uint32_t v_curr_2002_; lean_object* v___x_2003_; lean_object* v_s_2004_; uint32_t v___x_2005_; uint8_t v___x_2006_; 
v_inputString_2001_ = lean_ctor_get(v_toInputContext_1999_, 0);
v_curr_2002_ = lean_string_utf8_get_fast(v_inputString_2001_, v_pos_1998_);
v___x_2003_ = lean_string_utf8_next_fast(v_inputString_2001_, v_pos_1998_);
v_s_2004_ = l_Lean_Parser_ParserState_setPos(v_s_1997_, v___x_2003_);
v___x_2005_ = 34;
v___x_2006_ = lean_uint32_dec_eq(v_curr_2002_, v___x_2005_);
if (v___x_2006_ == 0)
{
uint32_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = 92;
v___x_2008_ = lean_uint32_dec_eq(v_curr_2002_, v___x_2007_);
if (v___x_2008_ == 0)
{
v_s_1997_ = v_s_2004_;
goto _start;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2011_ = lean_box(v___x_2008_);
v___x_2012_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2012_, 0, v_startPos_1994_);
lean_closure_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = l_Lean_Parser_andthenFn(v___x_2010_, v___x_2012_, v_c_1996_, v_s_2004_);
return v___x_2013_;
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2015_ = l_Lean_Parser_mkNodeToken(v___x_2014_, v_startPos_1994_, v_includeWhitespace_1995_, v_c_1996_, v_s_2004_);
return v___x_2015_;
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec_ref(v_c_1996_);
v___x_2016_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2017_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_1997_, v___x_2016_, v_startPos_1994_);
return v___x_2017_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2018_, lean_object* v_i_2019_){
_start:
{
lean_object* v_toInputContext_2020_; uint8_t v___x_2021_; 
v_toInputContext_2020_ = lean_ctor_get(v_c_2018_, 0);
v___x_2021_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2020_, v_i_2019_);
if (v___x_2021_ == 0)
{
lean_object* v_inputString_2022_; uint32_t v_curr_2023_; uint32_t v___x_2024_; uint8_t v___x_2025_; 
v_inputString_2022_ = lean_ctor_get(v_toInputContext_2020_, 0);
v_curr_2023_ = lean_string_utf8_get_fast(v_inputString_2022_, v_i_2019_);
v___x_2024_ = 35;
v___x_2025_ = lean_uint32_dec_eq(v_curr_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
uint32_t v___x_2026_; uint8_t v___x_2027_; 
lean_dec(v_i_2019_);
v___x_2026_ = 34;
v___x_2027_ = lean_uint32_dec_eq(v_curr_2023_, v___x_2026_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_string_utf8_next_fast(v_inputString_2022_, v_i_2019_);
lean_dec(v_i_2019_);
v_i_2019_ = v___x_2028_;
goto _start;
}
}
else
{
uint8_t v___x_2030_; 
lean_dec(v_i_2019_);
v___x_2030_ = 0;
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2031_, lean_object* v_i_2032_){
_start:
{
uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_res_2033_ = l_Lean_Parser_isRawStrLitStart(v_c_2031_, v_i_2032_);
lean_dec_ref(v_c_2031_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2036_, lean_object* v_s_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2039_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2037_, v___x_2038_, v_startPos_2036_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2040_, lean_object* v_num_2041_, lean_object* v_closingNum_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_pos_2045_; lean_object* v_toInputContext_2046_; uint8_t v___x_2047_; 
v_pos_2045_ = lean_ctor_get(v_a_2044_, 2);
v_toInputContext_2046_ = lean_ctor_get(v_a_2043_, 0);
v___x_2047_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2046_, v_pos_2045_);
if (v___x_2047_ == 0)
{
lean_object* v_inputString_2048_; uint32_t v_curr_2049_; lean_object* v___x_2050_; lean_object* v_s_2051_; uint32_t v___x_2052_; uint8_t v___x_2053_; 
v_inputString_2048_ = lean_ctor_get(v_toInputContext_2046_, 0);
v_curr_2049_ = lean_string_utf8_get_fast(v_inputString_2048_, v_pos_2045_);
v___x_2050_ = lean_string_utf8_next_fast(v_inputString_2048_, v_pos_2045_);
v_s_2051_ = l_Lean_Parser_ParserState_setPos(v_a_2044_, v___x_2050_);
v___x_2052_ = 35;
v___x_2053_ = lean_uint32_dec_eq(v_curr_2049_, v___x_2052_);
if (v___x_2053_ == 0)
{
uint32_t v___x_2054_; uint8_t v___x_2055_; 
lean_dec(v_closingNum_2042_);
v___x_2054_ = 34;
v___x_2055_ = lean_uint32_dec_eq(v_curr_2049_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2040_, v_num_2041_, v_a_2043_, v_s_2051_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v_closingNum_2042_ = v___x_2057_;
v_a_2044_ = v_s_2051_;
goto _start;
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = lean_nat_add(v_closingNum_2042_, v___x_2059_);
lean_dec(v_closingNum_2042_);
v___x_2061_ = lean_nat_dec_eq(v___x_2060_, v_num_2041_);
if (v___x_2061_ == 0)
{
v_closingNum_2042_ = v___x_2060_;
v_a_2044_ = v_s_2051_;
goto _start;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v___x_2060_);
v___x_2063_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2064_ = l_Lean_Parser_mkNodeToken(v___x_2063_, v_startPos_2040_, v___x_2061_, v_a_2043_, v_s_2051_);
return v___x_2064_;
}
}
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v_a_2043_);
lean_dec(v_closingNum_2042_);
v___x_2065_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2040_, v_a_2044_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2066_, lean_object* v_num_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_pos_2070_; lean_object* v_toInputContext_2071_; uint8_t v___x_2072_; 
v_pos_2070_ = lean_ctor_get(v_a_2069_, 2);
v_toInputContext_2071_ = lean_ctor_get(v_a_2068_, 0);
v___x_2072_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2071_, v_pos_2070_);
if (v___x_2072_ == 0)
{
lean_object* v_inputString_2073_; uint32_t v_curr_2074_; lean_object* v___x_2075_; lean_object* v_s_2076_; uint32_t v___x_2077_; uint8_t v___x_2078_; 
v_inputString_2073_ = lean_ctor_get(v_toInputContext_2071_, 0);
v_curr_2074_ = lean_string_utf8_get_fast(v_inputString_2073_, v_pos_2070_);
v___x_2075_ = lean_string_utf8_next_fast(v_inputString_2073_, v_pos_2070_);
v_s_2076_ = l_Lean_Parser_ParserState_setPos(v_a_2069_, v___x_2075_);
v___x_2077_ = 34;
v___x_2078_ = lean_uint32_dec_eq(v_curr_2074_, v___x_2077_);
if (v___x_2078_ == 0)
{
v_a_2069_ = v_s_2076_;
goto _start;
}
else
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_nat_dec_eq(v_num_2067_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2066_, v_num_2067_, v___x_2080_, v_a_2068_, v_s_2076_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2084_ = l_Lean_Parser_mkNodeToken(v___x_2083_, v_startPos_2066_, v___x_2081_, v_a_2068_, v_s_2076_);
return v___x_2084_;
}
}
}
else
{
lean_object* v___x_2085_; 
lean_dec_ref(v_a_2068_);
v___x_2085_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2066_, v_a_2069_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2086_, lean_object* v_num_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2086_, v_num_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_num_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2091_, lean_object* v_num_2092_, lean_object* v_closingNum_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2091_, v_num_2092_, v_closingNum_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_num_2092_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2097_, lean_object* v_num_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_pos_2101_; lean_object* v_toInputContext_2102_; uint8_t v___x_2103_; 
v_pos_2101_ = lean_ctor_get(v_a_2100_, 2);
v_toInputContext_2102_ = lean_ctor_get(v_a_2099_, 0);
v___x_2103_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2102_, v_pos_2101_);
if (v___x_2103_ == 0)
{
lean_object* v_inputString_2104_; uint32_t v_curr_2105_; lean_object* v___x_2106_; lean_object* v_s_2107_; uint32_t v___x_2108_; uint8_t v___x_2109_; 
v_inputString_2104_ = lean_ctor_get(v_toInputContext_2102_, 0);
v_curr_2105_ = lean_string_utf8_get_fast(v_inputString_2104_, v_pos_2101_);
v___x_2106_ = lean_string_utf8_next_fast(v_inputString_2104_, v_pos_2101_);
v_s_2107_ = l_Lean_Parser_ParserState_setPos(v_a_2100_, v___x_2106_);
v___x_2108_ = 35;
v___x_2109_ = lean_uint32_dec_eq(v_curr_2105_, v___x_2108_);
if (v___x_2109_ == 0)
{
uint32_t v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = 34;
v___x_2111_ = lean_uint32_dec_eq(v_curr_2105_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec_ref(v_a_2099_);
lean_dec(v_num_2098_);
v___x_2112_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2097_, v_s_2107_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2097_, v_num_2098_, v_a_2099_, v_s_2107_);
lean_dec(v_num_2098_);
return v___x_2113_;
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_add(v_num_2098_, v___x_2114_);
lean_dec(v_num_2098_);
v_num_2098_ = v___x_2115_;
v_a_2100_ = v_s_2107_;
goto _start;
}
}
else
{
lean_object* v___x_2117_; 
lean_dec_ref(v_a_2099_);
lean_dec(v_num_2098_);
v___x_2117_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2097_, v_a_2100_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2118_, v___x_2121_, v_a_2119_, v_a_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2124_, lean_object* v_expecting_2125_, uint8_t v_needDigit_2126_, lean_object* v_c_2127_, lean_object* v_s_2128_){
_start:
{
lean_object* v_pos_2129_; lean_object* v_toInputContext_2130_; uint8_t v___x_2131_; 
v_pos_2129_ = lean_ctor_get(v_s_2128_, 2);
v_toInputContext_2130_ = lean_ctor_get(v_c_2127_, 0);
v___x_2131_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2130_, v_pos_2129_);
if (v___x_2131_ == 0)
{
lean_object* v_inputString_2132_; uint8_t v___x_2133_; uint32_t v_curr_2134_; uint32_t v___x_2135_; uint8_t v___x_2136_; 
v_inputString_2132_ = lean_ctor_get(v_toInputContext_2130_, 0);
v___x_2133_ = 1;
v_curr_2134_ = lean_string_utf8_get_fast(v_inputString_2132_, v_pos_2129_);
v___x_2135_ = 95;
v___x_2136_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = lean_box_uint32(v_curr_2134_);
lean_inc_ref(v_isDigit_2124_);
v___x_2138_ = lean_apply_1(v_isDigit_2124_, v___x_2137_);
v___x_2139_ = lean_unbox(v___x_2138_);
if (v___x_2139_ == 0)
{
lean_dec_ref(v_isDigit_2124_);
if (v_needDigit_2126_ == 0)
{
lean_dec_ref(v_expecting_2125_);
return v_s_2128_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_expecting_2125_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2128_, v___x_2140_, v___x_2142_, v___x_2133_);
return v___x_2143_;
}
}
else
{
lean_object* v___x_2144_; 
lean_inc(v_pos_2129_);
v___x_2144_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2128_, v_c_2127_, v_pos_2129_);
lean_dec(v_pos_2129_);
v_needDigit_2126_ = v___x_2136_;
v_s_2128_ = v___x_2144_;
goto _start;
}
}
else
{
lean_object* v___x_2146_; 
lean_inc(v_pos_2129_);
v___x_2146_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2128_, v_c_2127_, v_pos_2129_);
lean_dec(v_pos_2129_);
v_needDigit_2126_ = v___x_2133_;
v_s_2128_ = v___x_2146_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2124_);
if (v_needDigit_2126_ == 0)
{
lean_dec_ref(v_expecting_2125_);
return v_s_2128_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_expecting_2125_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2128_, v___x_2149_);
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2151_, lean_object* v_expecting_2152_, lean_object* v_needDigit_2153_, lean_object* v_c_2154_, lean_object* v_s_2155_){
_start:
{
uint8_t v_needDigit_boxed_2156_; lean_object* v_res_2157_; 
v_needDigit_boxed_2156_ = lean_unbox(v_needDigit_2153_);
v_res_2157_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2151_, v_expecting_2152_, v_needDigit_boxed_2156_, v_c_2154_, v_s_2155_);
lean_dec_ref(v_c_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2158_){
_start:
{
uint32_t v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = 48;
v___x_2160_ = lean_uint32_dec_le(v___x_2159_, v_c_2158_);
if (v___x_2160_ == 0)
{
return v___x_2160_;
}
else
{
uint32_t v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = 57;
v___x_2162_ = lean_uint32_dec_le(v_c_2158_, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2163_){
_start:
{
uint32_t v_c_boxed_2164_; uint8_t v_res_2165_; lean_object* v_r_2166_; 
v_c_boxed_2164_ = lean_unbox_uint32(v_c_2163_);
lean_dec(v_c_2163_);
v_res_2165_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2164_);
v_r_2166_ = lean_box(v_res_2165_);
return v_r_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2171_, lean_object* v_c_2172_, lean_object* v_s_2173_, uint8_t v_hasBareDot_2174_){
_start:
{
lean_object* v_toInputContext_2175_; lean_object* v_pos_2176_; uint8_t v___x_2177_; 
v_toInputContext_2175_ = lean_ctor_get(v_c_2172_, 0);
v_pos_2176_ = lean_ctor_get(v_s_2173_, 2);
v___x_2177_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2175_, v_pos_2176_);
if (v___x_2177_ == 0)
{
lean_object* v_inputString_2178_; lean_object* v___f_2179_; uint8_t v___x_2180_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2191_; lean_object* v___y_2198_; lean_object* v___y_2199_; uint32_t v_curr_2213_; uint8_t v___y_2215_; uint8_t v___y_2219_; uint32_t v___x_2228_; uint8_t v___x_2229_; 
v_inputString_2178_ = lean_ctor_get(v_toInputContext_2175_, 0);
v___f_2179_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2180_ = 1;
v_curr_2213_ = lean_string_utf8_get_fast(v_inputString_2178_, v_pos_2176_);
v___x_2228_ = 101;
v___x_2229_ = lean_uint32_dec_eq(v_curr_2213_, v___x_2228_);
if (v___x_2229_ == 0)
{
uint32_t v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = 69;
v___x_2231_ = lean_uint32_dec_eq(v_curr_2213_, v___x_2230_);
if (v___x_2231_ == 0)
{
if (v_hasBareDot_2174_ == 0)
{
lean_dec(v_startPos_2171_);
return v_s_2173_;
}
else
{
uint32_t v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = 65;
v___x_2233_ = lean_uint32_dec_le(v___x_2232_, v_curr_2213_);
if (v___x_2233_ == 0)
{
goto v___jp_2223_;
}
else
{
uint32_t v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = 90;
v___x_2235_ = lean_uint32_dec_le(v_curr_2213_, v___x_2234_);
if (v___x_2235_ == 0)
{
goto v___jp_2223_;
}
else
{
goto v___jp_2208_;
}
}
}
}
else
{
lean_dec(v_startPos_2171_);
goto v___jp_2201_;
}
}
else
{
lean_dec(v_startPos_2171_);
goto v___jp_2201_;
}
v___jp_2181_:
{
if (v___y_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v___y_2182_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2185_ = lean_box(0);
v___x_2186_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2173_, v___x_2184_, v___x_2185_, v___x_2180_);
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2188_ = l_Lean_Parser_ParserState_setPos(v_s_2173_, v___y_2182_);
v___x_2189_ = l_Lean_Parser_takeDigitsFn(v___f_2179_, v___x_2187_, v___x_2177_, v_c_2172_, v___x_2188_);
return v___x_2189_;
}
}
v___jp_2190_:
{
uint32_t v_curr_2192_; uint32_t v___x_2193_; uint8_t v___x_2194_; 
v_curr_2192_ = lean_string_utf8_get(v_inputString_2178_, v___y_2191_);
v___x_2193_ = 48;
v___x_2194_ = lean_uint32_dec_le(v___x_2193_, v_curr_2192_);
if (v___x_2194_ == 0)
{
v___y_2182_ = v___y_2191_;
v___y_2183_ = v___x_2194_;
goto v___jp_2181_;
}
else
{
uint32_t v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = 57;
v___x_2196_ = lean_uint32_dec_le(v_curr_2192_, v___x_2195_);
v___y_2182_ = v___y_2191_;
v___y_2183_ = v___x_2196_;
goto v___jp_2181_;
}
}
v___jp_2197_:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_string_utf8_next(v___y_2199_, v___y_2198_);
lean_dec(v___y_2198_);
v___y_2191_ = v___x_2200_;
goto v___jp_2190_;
}
v___jp_2201_:
{
lean_object* v_i_2202_; uint32_t v___x_2203_; uint32_t v___x_2204_; uint8_t v___x_2205_; 
v_i_2202_ = lean_string_utf8_next(v_inputString_2178_, v_pos_2176_);
v___x_2203_ = lean_string_utf8_get(v_inputString_2178_, v_i_2202_);
v___x_2204_ = 45;
v___x_2205_ = lean_uint32_dec_eq(v___x_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
uint32_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = 43;
v___x_2207_ = lean_uint32_dec_eq(v___x_2203_, v___x_2206_);
if (v___x_2207_ == 0)
{
v___y_2191_ = v_i_2202_;
goto v___jp_2190_;
}
else
{
v___y_2198_ = v_i_2202_;
v___y_2199_ = v_inputString_2178_;
goto v___jp_2197_;
}
}
else
{
v___y_2198_ = v_i_2202_;
v___y_2199_ = v_inputString_2178_;
goto v___jp_2197_;
}
}
v___jp_2208_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2209_ = l_Lean_Parser_ParserState_setPos(v_s_2173_, v_startPos_2171_);
v___x_2210_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2211_ = lean_box(0);
v___x_2212_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2209_, v___x_2210_, v___x_2211_, v___x_2180_);
return v___x_2212_;
}
v___jp_2214_:
{
if (v___y_2215_ == 0)
{
uint32_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = 171;
v___x_2217_ = lean_uint32_dec_eq(v_curr_2213_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_dec(v_startPos_2171_);
return v_s_2173_;
}
else
{
goto v___jp_2208_;
}
}
else
{
goto v___jp_2208_;
}
}
v___jp_2218_:
{
if (v___y_2219_ == 0)
{
uint32_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = 95;
v___x_2221_ = lean_uint32_dec_eq(v_curr_2213_, v___x_2220_);
if (v___x_2221_ == 0)
{
uint8_t v___x_2222_; 
v___x_2222_ = l_Lean_isLetterLike(v_curr_2213_);
v___y_2215_ = v___x_2222_;
goto v___jp_2214_;
}
else
{
v___y_2215_ = v___x_2221_;
goto v___jp_2214_;
}
}
else
{
goto v___jp_2208_;
}
}
v___jp_2223_:
{
uint32_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = 97;
v___x_2225_ = lean_uint32_dec_le(v___x_2224_, v_curr_2213_);
if (v___x_2225_ == 0)
{
v___y_2219_ = v___x_2225_;
goto v___jp_2218_;
}
else
{
uint32_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = 122;
v___x_2227_ = lean_uint32_dec_le(v_curr_2213_, v___x_2226_);
v___y_2219_ = v___x_2227_;
goto v___jp_2218_;
}
}
}
else
{
lean_dec(v_startPos_2171_);
return v_s_2173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2236_, lean_object* v_c_2237_, lean_object* v_s_2238_, lean_object* v_hasBareDot_2239_){
_start:
{
uint8_t v_hasBareDot_boxed_2240_; lean_object* v_res_2241_; 
v_hasBareDot_boxed_2240_ = lean_unbox(v_hasBareDot_2239_);
v_res_2241_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2236_, v_c_2237_, v_s_2238_, v_hasBareDot_boxed_2240_);
lean_dec_ref(v_c_2237_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2242_, lean_object* v_s_2243_){
_start:
{
lean_object* v_toInputContext_2244_; lean_object* v_pos_2245_; lean_object* v_inputString_2246_; uint32_t v_curr_2247_; uint32_t v___x_2248_; uint8_t v___x_2249_; 
v_toInputContext_2244_ = lean_ctor_get(v_c_2242_, 0);
v_pos_2245_ = lean_ctor_get(v_s_2243_, 2);
v_inputString_2246_ = lean_ctor_get(v_toInputContext_2244_, 0);
v_curr_2247_ = lean_string_utf8_get(v_inputString_2246_, v_pos_2245_);
v___x_2248_ = 46;
v___x_2249_ = lean_uint32_dec_eq(v_curr_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_box(v___x_2249_);
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_s_2243_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
return v___x_2251_;
}
else
{
lean_object* v___f_2252_; lean_object* v_i_2253_; uint8_t v___y_2255_; uint32_t v_curr_2265_; uint32_t v___x_2266_; uint8_t v___x_2267_; 
v___f_2252_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_i_2253_ = lean_string_utf8_next(v_inputString_2246_, v_pos_2245_);
v_curr_2265_ = lean_string_utf8_get(v_inputString_2246_, v_i_2253_);
v___x_2266_ = 48;
v___x_2267_ = lean_uint32_dec_le(v___x_2266_, v_curr_2265_);
if (v___x_2267_ == 0)
{
v___y_2255_ = v___x_2267_;
goto v___jp_2254_;
}
else
{
uint32_t v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = 57;
v___x_2269_ = lean_uint32_dec_le(v_curr_2265_, v___x_2268_);
v___y_2255_ = v___x_2269_;
goto v___jp_2254_;
}
v___jp_2254_:
{
if (v___y_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = l_Lean_Parser_ParserState_setPos(v_s_2243_, v_i_2253_);
v___x_2257_ = lean_box(v___x_2249_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2260_ = 0;
v___x_2261_ = l_Lean_Parser_ParserState_setPos(v_s_2243_, v_i_2253_);
v___x_2262_ = l_Lean_Parser_takeDigitsFn(v___f_2252_, v___x_2259_, v___x_2260_, v_c_2242_, v___x_2261_);
v___x_2263_ = lean_box(v___x_2260_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2270_, lean_object* v_s_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2270_, v_s_2271_);
lean_dec_ref(v_c_2270_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2276_, uint8_t v_includeWhitespace_2277_, lean_object* v_c_2278_, lean_object* v_s_2279_){
_start:
{
lean_object* v___x_2280_; lean_object* v_fst_2281_; lean_object* v_snd_2282_; uint8_t v___x_2283_; lean_object* v_s_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2280_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2278_, v_s_2279_);
v_fst_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_fst_2281_);
v_snd_2282_ = lean_ctor_get(v___x_2280_, 1);
lean_inc(v_snd_2282_);
lean_dec_ref(v___x_2280_);
v___x_2283_ = lean_unbox(v_snd_2282_);
lean_dec(v_snd_2282_);
lean_inc(v_startPos_2276_);
v_s_2284_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2276_, v_c_2278_, v_fst_2281_, v___x_2283_);
v___x_2285_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2286_ = l_Lean_Parser_mkNodeToken(v___x_2285_, v_startPos_2276_, v_includeWhitespace_2277_, v_c_2278_, v_s_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2287_, lean_object* v_includeWhitespace_2288_, lean_object* v_c_2289_, lean_object* v_s_2290_){
_start:
{
uint8_t v_includeWhitespace_boxed_2291_; lean_object* v_res_2292_; 
v_includeWhitespace_boxed_2291_ = lean_unbox(v_includeWhitespace_2288_);
v_res_2292_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2287_, v_includeWhitespace_boxed_2291_, v_c_2289_, v_s_2290_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2296_, uint8_t v_includeWhitespace_2297_, lean_object* v_c_2298_, lean_object* v_s_2299_){
_start:
{
lean_object* v___f_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v_s_2303_; lean_object* v_pos_2304_; lean_object* v_toInputContext_2305_; uint8_t v___x_2306_; 
v___f_2300_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2301_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2302_ = 0;
v_s_2303_ = l_Lean_Parser_takeDigitsFn(v___f_2300_, v___x_2301_, v___x_2302_, v_c_2298_, v_s_2299_);
v_pos_2304_ = lean_ctor_get(v_s_2303_, 2);
lean_inc(v_pos_2304_);
v_toInputContext_2305_ = lean_ctor_get(v_c_2298_, 0);
v___x_2306_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2305_, v_pos_2304_);
if (v___x_2306_ == 0)
{
lean_object* v_inputString_2307_; uint32_t v_curr_2308_; uint8_t v___y_2322_; lean_object* v_j_2325_; uint8_t v___x_2331_; 
v_inputString_2307_ = lean_ctor_get(v_toInputContext_2305_, 0);
v_curr_2308_ = lean_string_utf8_get_fast(v_inputString_2307_, v_pos_2304_);
v_j_2325_ = lean_string_utf8_next(v_inputString_2307_, v_pos_2304_);
lean_dec(v_pos_2304_);
v___x_2331_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2305_, v_j_2325_);
if (v___x_2331_ == 0)
{
goto v___jp_2326_;
}
else
{
if (v___x_2306_ == 0)
{
lean_dec(v_j_2325_);
goto v___jp_2309_;
}
else
{
goto v___jp_2326_;
}
}
v___jp_2309_:
{
uint32_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = 46;
v___x_2311_ = lean_uint32_dec_eq(v_curr_2308_, v___x_2310_);
if (v___x_2311_ == 0)
{
uint32_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = 101;
v___x_2313_ = lean_uint32_dec_eq(v_curr_2308_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint32_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = 69;
v___x_2315_ = lean_uint32_dec_eq(v_curr_2308_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2317_ = l_Lean_Parser_mkNodeToken(v___x_2316_, v_startPos_2296_, v_includeWhitespace_2297_, v_c_2298_, v_s_2303_);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2296_, v_includeWhitespace_2297_, v_c_2298_, v_s_2303_);
return v___x_2318_;
}
}
else
{
lean_object* v___x_2319_; 
v___x_2319_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2296_, v_includeWhitespace_2297_, v_c_2298_, v_s_2303_);
return v___x_2319_;
}
}
else
{
lean_object* v___x_2320_; 
v___x_2320_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2296_, v_includeWhitespace_2297_, v_c_2298_, v_s_2303_);
return v___x_2320_;
}
}
v___jp_2321_:
{
if (v___y_2322_ == 0)
{
goto v___jp_2309_;
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2324_ = l_Lean_Parser_mkNodeToken(v___x_2323_, v_startPos_2296_, v_includeWhitespace_2297_, v_c_2298_, v_s_2303_);
return v___x_2324_;
}
}
v___jp_2326_:
{
uint32_t v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = 46;
v___x_2328_ = lean_uint32_dec_eq(v_curr_2308_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec(v_j_2325_);
v___y_2322_ = v___x_2328_;
goto v___jp_2321_;
}
else
{
uint32_t v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = lean_string_utf8_get_fast(v_inputString_2307_, v_j_2325_);
lean_dec(v_j_2325_);
v___x_2330_ = lean_uint32_dec_eq(v___x_2329_, v___x_2327_);
v___y_2322_ = v___x_2330_;
goto v___jp_2321_;
}
}
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec(v_pos_2304_);
v___x_2332_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2333_ = l_Lean_Parser_mkNodeToken(v___x_2332_, v_startPos_2296_, v___x_2306_, v_c_2298_, v_s_2303_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2334_, lean_object* v_includeWhitespace_2335_, lean_object* v_c_2336_, lean_object* v_s_2337_){
_start:
{
uint8_t v_includeWhitespace_boxed_2338_; lean_object* v_res_2339_; 
v_includeWhitespace_boxed_2338_ = lean_unbox(v_includeWhitespace_2335_);
v_res_2339_ = l_Lean_Parser_decimalNumberFn(v_startPos_2334_, v_includeWhitespace_boxed_2338_, v_c_2336_, v_s_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2340_){
_start:
{
uint32_t v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = 48;
v___x_2342_ = lean_uint32_dec_eq(v_c_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
uint32_t v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = 49;
v___x_2344_ = lean_uint32_dec_eq(v_c_2340_, v___x_2343_);
return v___x_2344_;
}
else
{
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2345_){
_start:
{
uint32_t v_c_boxed_2346_; uint8_t v_res_2347_; lean_object* v_r_2348_; 
v_c_boxed_2346_ = lean_unbox_uint32(v_c_2345_);
lean_dec(v_c_2345_);
v_res_2347_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2346_);
v_r_2348_ = lean_box(v_res_2347_);
return v_r_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2351_, uint8_t v_includeWhitespace_2352_, lean_object* v_c_2353_, lean_object* v_s_2354_){
_start:
{
lean_object* v___f_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v_s_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___f_2355_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2356_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2357_ = 1;
v_s_2358_ = l_Lean_Parser_takeDigitsFn(v___f_2355_, v___x_2356_, v___x_2357_, v_c_2353_, v_s_2354_);
v___x_2359_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2360_ = l_Lean_Parser_mkNodeToken(v___x_2359_, v_startPos_2351_, v_includeWhitespace_2352_, v_c_2353_, v_s_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2361_, lean_object* v_includeWhitespace_2362_, lean_object* v_c_2363_, lean_object* v_s_2364_){
_start:
{
uint8_t v_includeWhitespace_boxed_2365_; lean_object* v_res_2366_; 
v_includeWhitespace_boxed_2365_ = lean_unbox(v_includeWhitespace_2362_);
v_res_2366_ = l_Lean_Parser_binNumberFn(v_startPos_2361_, v_includeWhitespace_boxed_2365_, v_c_2363_, v_s_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2367_){
_start:
{
uint32_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = 48;
v___x_2369_ = lean_uint32_dec_le(v___x_2368_, v_c_2367_);
if (v___x_2369_ == 0)
{
return v___x_2369_;
}
else
{
uint32_t v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = 55;
v___x_2371_ = lean_uint32_dec_le(v_c_2367_, v___x_2370_);
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2372_){
_start:
{
uint32_t v_c_boxed_2373_; uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_c_boxed_2373_ = lean_unbox_uint32(v_c_2372_);
lean_dec(v_c_2372_);
v_res_2374_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2373_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2378_, uint8_t v_includeWhitespace_2379_, lean_object* v_c_2380_, lean_object* v_s_2381_){
_start:
{
lean_object* v___f_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; lean_object* v_s_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___f_2382_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2383_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2384_ = 1;
v_s_2385_ = l_Lean_Parser_takeDigitsFn(v___f_2382_, v___x_2383_, v___x_2384_, v_c_2380_, v_s_2381_);
v___x_2386_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2387_ = l_Lean_Parser_mkNodeToken(v___x_2386_, v_startPos_2378_, v_includeWhitespace_2379_, v_c_2380_, v_s_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2388_, lean_object* v_includeWhitespace_2389_, lean_object* v_c_2390_, lean_object* v_s_2391_){
_start:
{
uint8_t v_includeWhitespace_boxed_2392_; lean_object* v_res_2393_; 
v_includeWhitespace_boxed_2392_ = lean_unbox(v_includeWhitespace_2389_);
v_res_2393_ = l_Lean_Parser_octalNumberFn(v_startPos_2388_, v_includeWhitespace_boxed_2392_, v_c_2390_, v_s_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2394_){
_start:
{
uint8_t v___y_2396_; uint8_t v___y_2402_; uint32_t v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = 48;
v___x_2408_ = lean_uint32_dec_le(v___x_2407_, v_c_2394_);
if (v___x_2408_ == 0)
{
v___y_2402_ = v___x_2408_;
goto v___jp_2401_;
}
else
{
uint32_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = 57;
v___x_2410_ = lean_uint32_dec_le(v_c_2394_, v___x_2409_);
v___y_2402_ = v___x_2410_;
goto v___jp_2401_;
}
v___jp_2395_:
{
if (v___y_2396_ == 0)
{
uint32_t v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = 65;
v___x_2398_ = lean_uint32_dec_le(v___x_2397_, v_c_2394_);
if (v___x_2398_ == 0)
{
return v___x_2398_;
}
else
{
uint32_t v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = 70;
v___x_2400_ = lean_uint32_dec_le(v_c_2394_, v___x_2399_);
return v___x_2400_;
}
}
else
{
return v___y_2396_;
}
}
v___jp_2401_:
{
if (v___y_2402_ == 0)
{
uint32_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = 97;
v___x_2404_ = lean_uint32_dec_le(v___x_2403_, v_c_2394_);
if (v___x_2404_ == 0)
{
v___y_2396_ = v___x_2404_;
goto v___jp_2395_;
}
else
{
uint32_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = 102;
v___x_2406_ = lean_uint32_dec_le(v_c_2394_, v___x_2405_);
v___y_2396_ = v___x_2406_;
goto v___jp_2395_;
}
}
else
{
return v___y_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2411_){
_start:
{
uint32_t v_c_boxed_2412_; uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_c_boxed_2412_ = lean_unbox_uint32(v_c_2411_);
lean_dec(v_c_2411_);
v_res_2413_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2412_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2415_){
_start:
{
uint8_t v___y_2417_; uint8_t v___y_2423_; uint32_t v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = 48;
v___x_2429_ = lean_uint32_dec_le(v___x_2428_, v___y_2415_);
if (v___x_2429_ == 0)
{
v___y_2423_ = v___x_2429_;
goto v___jp_2422_;
}
else
{
uint32_t v___x_2430_; uint8_t v___x_2431_; 
v___x_2430_ = 57;
v___x_2431_ = lean_uint32_dec_le(v___y_2415_, v___x_2430_);
v___y_2423_ = v___x_2431_;
goto v___jp_2422_;
}
v___jp_2416_:
{
if (v___y_2417_ == 0)
{
uint32_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = 65;
v___x_2419_ = lean_uint32_dec_le(v___x_2418_, v___y_2415_);
if (v___x_2419_ == 0)
{
return v___x_2419_;
}
else
{
uint32_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = 70;
v___x_2421_ = lean_uint32_dec_le(v___y_2415_, v___x_2420_);
return v___x_2421_;
}
}
else
{
return v___y_2417_;
}
}
v___jp_2422_:
{
if (v___y_2423_ == 0)
{
uint32_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = 97;
v___x_2425_ = lean_uint32_dec_le(v___x_2424_, v___y_2415_);
if (v___x_2425_ == 0)
{
v___y_2417_ = v___x_2425_;
goto v___jp_2416_;
}
else
{
uint32_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = 102;
v___x_2427_ = lean_uint32_dec_le(v___y_2415_, v___x_2426_);
v___y_2417_ = v___x_2427_;
goto v___jp_2416_;
}
}
else
{
return v___y_2423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2432_){
_start:
{
uint32_t v___y_54__boxed_2433_; uint8_t v_res_2434_; lean_object* v_r_2435_; 
v___y_54__boxed_2433_ = lean_unbox_uint32(v___y_2432_);
lean_dec(v___y_2432_);
v_res_2434_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_54__boxed_2433_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2438_, uint8_t v_includeWhitespace_2439_, lean_object* v_kind_2440_, lean_object* v_c_2441_, lean_object* v_s_2442_){
_start:
{
lean_object* v___f_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v_s_2446_; lean_object* v___x_2447_; 
v___f_2443_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2444_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2445_ = 1;
v_s_2446_ = l_Lean_Parser_takeDigitsFn(v___f_2443_, v___x_2444_, v___x_2445_, v_c_2441_, v_s_2442_);
v___x_2447_ = l_Lean_Parser_mkNodeToken(v_kind_2440_, v_startPos_2438_, v_includeWhitespace_2439_, v_c_2441_, v_s_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2448_, lean_object* v_includeWhitespace_2449_, lean_object* v_kind_2450_, lean_object* v_c_2451_, lean_object* v_s_2452_){
_start:
{
uint8_t v_includeWhitespace_boxed_2453_; lean_object* v_res_2454_; 
v_includeWhitespace_boxed_2453_ = lean_unbox(v_includeWhitespace_2449_);
v_res_2454_ = l_Lean_Parser_hexNumberFn(v_startPos_2448_, v_includeWhitespace_boxed_2453_, v_kind_2450_, v_c_2451_, v_s_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2456_, lean_object* v_c_2457_, lean_object* v_s_2458_){
_start:
{
lean_object* v_pos_2459_; uint8_t v___y_2461_; lean_object* v_toInputContext_2466_; uint8_t v___x_2467_; 
v_pos_2459_ = lean_ctor_get(v_s_2458_, 2);
v_toInputContext_2466_ = lean_ctor_get(v_c_2457_, 0);
v___x_2467_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2466_, v_pos_2459_);
if (v___x_2467_ == 0)
{
lean_object* v_inputString_2468_; uint32_t v_curr_2469_; uint32_t v___x_2470_; uint8_t v___x_2471_; 
v_inputString_2468_ = lean_ctor_get(v_toInputContext_2466_, 0);
v_curr_2469_ = lean_string_utf8_get_fast(v_inputString_2468_, v_pos_2459_);
v___x_2470_ = 48;
v___x_2471_ = lean_uint32_dec_eq(v_curr_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_uint32_dec_le(v___x_2470_, v_curr_2469_);
if (v___x_2472_ == 0)
{
v___y_2461_ = v___x_2472_;
goto v___jp_2460_;
}
else
{
uint32_t v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = 57;
v___x_2474_ = lean_uint32_dec_le(v_curr_2469_, v___x_2473_);
v___y_2461_ = v___x_2474_;
goto v___jp_2460_;
}
}
else
{
lean_object* v_i_2475_; uint32_t v_curr_2486_; uint32_t v___x_2487_; uint8_t v___x_2488_; 
lean_inc(v_pos_2459_);
v_i_2475_ = lean_string_utf8_next_fast(v_inputString_2468_, v_pos_2459_);
v_curr_2486_ = lean_string_utf8_get(v_inputString_2468_, v_i_2475_);
v___x_2487_ = 98;
v___x_2488_ = lean_uint32_dec_eq(v_curr_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
uint32_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = 66;
v___x_2490_ = lean_uint32_dec_eq(v_curr_2486_, v___x_2489_);
if (v___x_2490_ == 0)
{
uint32_t v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = 111;
v___x_2492_ = lean_uint32_dec_eq(v_curr_2486_, v___x_2491_);
if (v___x_2492_ == 0)
{
uint32_t v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = 79;
v___x_2494_ = lean_uint32_dec_eq(v_curr_2486_, v___x_2493_);
if (v___x_2494_ == 0)
{
uint32_t v___x_2495_; uint8_t v___x_2496_; 
v___x_2495_ = 120;
v___x_2496_ = lean_uint32_dec_eq(v_curr_2486_, v___x_2495_);
if (v___x_2496_ == 0)
{
uint32_t v___x_2497_; uint8_t v___x_2498_; 
v___x_2497_ = 88;
v___x_2498_ = lean_uint32_dec_eq(v_curr_2486_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = l_Lean_Parser_ParserState_setPos(v_s_2458_, v_i_2475_);
v___x_2500_ = l_Lean_Parser_decimalNumberFn(v_pos_2459_, v_includeWhitespace_2456_, v_c_2457_, v___x_2499_);
return v___x_2500_;
}
else
{
goto v___jp_2476_;
}
}
else
{
goto v___jp_2476_;
}
}
else
{
goto v___jp_2480_;
}
}
else
{
goto v___jp_2480_;
}
}
else
{
goto v___jp_2483_;
}
}
else
{
goto v___jp_2483_;
}
v___jp_2476_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2478_ = l_Lean_Parser_ParserState_next(v_s_2458_, v_c_2457_, v_i_2475_);
v___x_2479_ = l_Lean_Parser_hexNumberFn(v_pos_2459_, v_includeWhitespace_2456_, v___x_2477_, v_c_2457_, v___x_2478_);
return v___x_2479_;
}
v___jp_2480_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = l_Lean_Parser_ParserState_next(v_s_2458_, v_c_2457_, v_i_2475_);
v___x_2482_ = l_Lean_Parser_octalNumberFn(v_pos_2459_, v_includeWhitespace_2456_, v_c_2457_, v___x_2481_);
return v___x_2482_;
}
v___jp_2483_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = l_Lean_Parser_ParserState_next(v_s_2458_, v_c_2457_, v_i_2475_);
v___x_2485_ = l_Lean_Parser_binNumberFn(v_pos_2459_, v_includeWhitespace_2456_, v_c_2457_, v___x_2484_);
return v___x_2485_;
}
}
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec_ref(v_c_2457_);
v___x_2501_ = lean_box(0);
v___x_2502_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2458_, v___x_2501_);
return v___x_2502_;
}
v___jp_2460_:
{
if (v___y_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec_ref(v_c_2457_);
v___x_2462_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2463_ = l_Lean_Parser_ParserState_mkError(v_s_2458_, v___x_2462_);
return v___x_2463_;
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_inc(v_pos_2459_);
v___x_2464_ = l_Lean_Parser_ParserState_next(v_s_2458_, v_c_2457_, v_pos_2459_);
v___x_2465_ = l_Lean_Parser_decimalNumberFn(v_pos_2459_, v_includeWhitespace_2456_, v_c_2457_, v___x_2464_);
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2503_, lean_object* v_c_2504_, lean_object* v_s_2505_){
_start:
{
uint8_t v_includeWhitespace_boxed_2506_; lean_object* v_res_2507_; 
v_includeWhitespace_boxed_2506_ = lean_unbox(v_includeWhitespace_2503_);
v_res_2507_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2506_, v_c_2504_, v_s_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2508_, lean_object* v_s_2509_){
_start:
{
lean_object* v_toInputContext_2510_; lean_object* v_pos_2511_; lean_object* v_inputString_2512_; uint32_t v_curr_2513_; uint32_t v___x_2514_; uint8_t v___x_2515_; 
v_toInputContext_2510_ = lean_ctor_get(v_c_2508_, 0);
v_pos_2511_ = lean_ctor_get(v_s_2509_, 2);
v_inputString_2512_ = lean_ctor_get(v_toInputContext_2510_, 0);
v_curr_2513_ = lean_string_utf8_get(v_inputString_2512_, v_pos_2511_);
v___x_2514_ = 46;
v___x_2515_ = lean_uint32_dec_eq(v_curr_2513_, v___x_2514_);
if (v___x_2515_ == 0)
{
return v___x_2515_;
}
else
{
lean_object* v_i_2516_; uint8_t v___x_2517_; 
v_i_2516_ = lean_string_utf8_next(v_inputString_2512_, v_pos_2511_);
v___x_2517_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2510_, v_i_2516_);
if (v___x_2517_ == 0)
{
uint32_t v_curr_2518_; uint8_t v___y_2520_; uint8_t v___y_2524_; uint32_t v___x_2533_; uint8_t v___x_2534_; 
v_curr_2518_ = lean_string_utf8_get(v_inputString_2512_, v_i_2516_);
lean_dec(v_i_2516_);
v___x_2533_ = 65;
v___x_2534_ = lean_uint32_dec_le(v___x_2533_, v_curr_2518_);
if (v___x_2534_ == 0)
{
goto v___jp_2528_;
}
else
{
uint32_t v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = 90;
v___x_2536_ = lean_uint32_dec_le(v_curr_2518_, v___x_2535_);
if (v___x_2536_ == 0)
{
goto v___jp_2528_;
}
else
{
return v___x_2515_;
}
}
v___jp_2519_:
{
if (v___y_2520_ == 0)
{
uint32_t v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = 171;
v___x_2522_ = lean_uint32_dec_eq(v_curr_2518_, v___x_2521_);
return v___x_2522_;
}
else
{
return v___x_2515_;
}
}
v___jp_2523_:
{
if (v___y_2524_ == 0)
{
uint32_t v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = 95;
v___x_2526_ = lean_uint32_dec_eq(v_curr_2518_, v___x_2525_);
if (v___x_2526_ == 0)
{
uint8_t v___x_2527_; 
v___x_2527_ = l_Lean_isLetterLike(v_curr_2518_);
v___y_2520_ = v___x_2527_;
goto v___jp_2519_;
}
else
{
v___y_2520_ = v___x_2526_;
goto v___jp_2519_;
}
}
else
{
return v___x_2515_;
}
}
v___jp_2528_:
{
uint32_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = 97;
v___x_2530_ = lean_uint32_dec_le(v___x_2529_, v_curr_2518_);
if (v___x_2530_ == 0)
{
v___y_2524_ = v___x_2530_;
goto v___jp_2523_;
}
else
{
uint32_t v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = 122;
v___x_2532_ = lean_uint32_dec_le(v_curr_2518_, v___x_2531_);
v___y_2524_ = v___x_2532_;
goto v___jp_2523_;
}
}
}
else
{
uint8_t v___x_2537_; 
lean_dec(v_i_2516_);
v___x_2537_ = 0;
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2538_, lean_object* v_s_2539_){
_start:
{
uint8_t v_res_2540_; lean_object* v_r_2541_; 
v_res_2540_ = l_Lean_Parser_isIdCont(v_c_2538_, v_s_2539_);
lean_dec_ref(v_s_2539_);
lean_dec_ref(v_c_2538_);
v_r_2541_ = lean_box(v_res_2540_);
return v_r_2541_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2542_, lean_object* v_idStopPos_2543_, lean_object* v_tk_2544_){
_start:
{
if (lean_obj_tag(v_tk_2544_) == 0)
{
uint8_t v___x_2545_; 
v___x_2545_ = 0;
return v___x_2545_;
}
else
{
lean_object* v_val_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_val_2546_ = lean_ctor_get(v_tk_2544_, 0);
v___x_2547_ = lean_nat_sub(v_idStopPos_2543_, v_idStartPos_2542_);
v___x_2548_ = lean_string_utf8_byte_size(v_val_2546_);
v___x_2549_ = lean_nat_dec_le(v___x_2547_, v___x_2548_);
lean_dec(v___x_2547_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2550_, lean_object* v_idStopPos_2551_, lean_object* v_tk_2552_){
_start:
{
uint8_t v_res_2553_; lean_object* v_r_2554_; 
v_res_2553_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2550_, v_idStopPos_2551_, v_tk_2552_);
lean_dec(v_tk_2552_);
lean_dec(v_idStopPos_2551_);
lean_dec(v_idStartPos_2550_);
v_r_2554_ = lean_box(v_res_2553_);
return v_r_2554_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object* v_a_2555_, lean_object* v_as_2556_, size_t v_i_2557_, size_t v_stop_2558_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_eq(v_i_2557_, v_stop_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = lean_array_uget_borrowed(v_as_2556_, v_i_2557_);
v___x_2561_ = lean_string_dec_eq(v_a_2555_, v___x_2560_);
if (v___x_2561_ == 0)
{
size_t v___x_2562_; size_t v___x_2563_; 
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_add(v_i_2557_, v___x_2562_);
v_i_2557_ = v___x_2563_;
goto _start;
}
else
{
return v___x_2561_;
}
}
else
{
uint8_t v___x_2565_; 
v___x_2565_ = 0;
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object* v_a_2566_, lean_object* v_as_2567_, lean_object* v_i_2568_, lean_object* v_stop_2569_){
_start:
{
size_t v_i_boxed_2570_; size_t v_stop_boxed_2571_; uint8_t v_res_2572_; lean_object* v_r_2573_; 
v_i_boxed_2570_ = lean_unbox_usize(v_i_2568_);
lean_dec(v_i_2568_);
v_stop_boxed_2571_ = lean_unbox_usize(v_stop_2569_);
lean_dec(v_stop_2569_);
v_res_2572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2566_, v_as_2567_, v_i_boxed_2570_, v_stop_boxed_2571_);
lean_dec_ref(v_as_2567_);
lean_dec_ref(v_a_2566_);
v_r_2573_ = lean_box(v_res_2572_);
return v_r_2573_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_as_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_array_get_size(v_as_2574_);
v___x_2578_ = lean_nat_dec_lt(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
return v___x_2578_;
}
else
{
if (v___x_2578_ == 0)
{
return v___x_2578_;
}
else
{
size_t v___x_2579_; size_t v___x_2580_; uint8_t v___x_2581_; 
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = lean_usize_of_nat(v___x_2577_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2575_, v_as_2574_, v___x_2579_, v___x_2580_);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_as_2582_, lean_object* v_a_2583_){
_start:
{
uint8_t v_res_2584_; lean_object* v_r_2585_; 
v_res_2584_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2582_, v_a_2583_);
lean_dec_ref(v_a_2583_);
lean_dec_ref(v_as_2582_);
v_r_2585_ = lean_box(v_res_2584_);
return v_r_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2588_, lean_object* v_tk_2589_, lean_object* v_c_2590_, lean_object* v_s_2591_){
_start:
{
if (lean_obj_tag(v_tk_2589_) == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec_ref(v_c_2590_);
v___x_2592_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2593_ = lean_box(0);
v___x_2594_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2591_, v___x_2592_, v_startPos_2588_, v___x_2593_);
return v___x_2594_;
}
else
{
lean_object* v_toCacheableParserContext_2595_; lean_object* v_val_2596_; lean_object* v_toInputContext_2597_; lean_object* v_forbiddenTks_2598_; uint8_t v___x_2599_; 
v_toCacheableParserContext_2595_ = lean_ctor_get(v_c_2590_, 2);
v_val_2596_ = lean_ctor_get(v_tk_2589_, 0);
v_toInputContext_2597_ = lean_ctor_get(v_c_2590_, 0);
lean_inc_ref(v_toInputContext_2597_);
v_forbiddenTks_2598_ = lean_ctor_get(v_toCacheableParserContext_2595_, 3);
v___x_2599_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_2598_, v_val_2596_);
if (v___x_2599_ == 0)
{
lean_object* v_leading_2600_; lean_object* v___x_2601_; lean_object* v_stopPos_2602_; lean_object* v_s_2603_; lean_object* v_s_2604_; lean_object* v___y_2606_; lean_object* v_pos_2610_; lean_object* v_inputString_2611_; lean_object* v_endPos_2612_; uint8_t v___x_2613_; 
lean_inc(v_startPos_2588_);
v_leading_2600_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2590_, v_startPos_2588_);
v___x_2601_ = lean_string_utf8_byte_size(v_val_2596_);
v_stopPos_2602_ = lean_nat_add(v_startPos_2588_, v___x_2601_);
lean_inc(v_stopPos_2602_);
v_s_2603_ = l_Lean_Parser_ParserState_setPos(v_s_2591_, v_stopPos_2602_);
v_s_2604_ = l_Lean_Parser_whitespace(v_c_2590_, v_s_2603_);
v_pos_2610_ = lean_ctor_get(v_s_2604_, 2);
lean_inc(v_pos_2610_);
v_inputString_2611_ = lean_ctor_get(v_toInputContext_2597_, 0);
lean_inc_ref(v_inputString_2611_);
v_endPos_2612_ = lean_ctor_get(v_toInputContext_2597_, 3);
lean_inc(v_endPos_2612_);
lean_dec_ref(v_toInputContext_2597_);
v___x_2613_ = lean_nat_dec_le(v_pos_2610_, v_endPos_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_dec(v_pos_2610_);
lean_inc(v_stopPos_2602_);
v___x_2614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2614_, 0, v_inputString_2611_);
lean_ctor_set(v___x_2614_, 1, v_stopPos_2602_);
lean_ctor_set(v___x_2614_, 2, v_endPos_2612_);
v___y_2606_ = v___x_2614_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2615_; 
lean_dec(v_endPos_2612_);
lean_inc(v_stopPos_2602_);
v___x_2615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2615_, 0, v_inputString_2611_);
lean_ctor_set(v___x_2615_, 1, v_stopPos_2602_);
lean_ctor_set(v___x_2615_, 2, v_pos_2610_);
v___y_2606_ = v___x_2615_;
goto v___jp_2605_;
}
v___jp_2605_:
{
lean_object* v___x_2607_; lean_object* v_atom_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2607_, 0, v_leading_2600_);
lean_ctor_set(v___x_2607_, 1, v_startPos_2588_);
lean_ctor_set(v___x_2607_, 2, v___y_2606_);
lean_ctor_set(v___x_2607_, 3, v_stopPos_2602_);
lean_inc(v_val_2596_);
v_atom_2608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2608_, 0, v___x_2607_);
lean_ctor_set(v_atom_2608_, 1, v_val_2596_);
v___x_2609_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2604_, v_atom_2608_);
return v___x_2609_;
}
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec_ref(v_toInputContext_2597_);
lean_dec_ref(v_c_2590_);
v___x_2616_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2617_ = lean_box(0);
v___x_2618_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2591_, v___x_2616_, v_startPos_2588_, v___x_2617_);
return v___x_2618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2619_, lean_object* v_tk_2620_, lean_object* v_c_2621_, lean_object* v_s_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2619_, v_tk_2620_, v_c_2621_, v_s_2622_);
lean_dec(v_tk_2620_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2624_, lean_object* v_tk_2625_, lean_object* v_val_2626_, uint8_t v_includeWhitespace_2627_, lean_object* v_c_2628_, lean_object* v_s_2629_){
_start:
{
lean_object* v_pos_2630_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___x_2640_; 
v_pos_2630_ = lean_ctor_get(v_s_2629_, 2);
v___x_2640_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2624_, v_pos_2630_, v_tk_2625_);
if (v___x_2640_ == 0)
{
lean_object* v_toInputContext_2641_; lean_object* v_inputString_2642_; lean_object* v_endPos_2643_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v_pos_2647_; lean_object* v___y_2653_; uint8_t v___x_2656_; 
lean_inc(v_pos_2630_);
v_toInputContext_2641_ = lean_ctor_get(v_c_2628_, 0);
v_inputString_2642_ = lean_ctor_get(v_toInputContext_2641_, 0);
lean_inc_ref(v_inputString_2642_);
v_endPos_2643_ = lean_ctor_get(v_toInputContext_2641_, 3);
lean_inc(v_endPos_2643_);
v___x_2656_ = lean_nat_dec_le(v_pos_2630_, v_endPos_2643_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_inc(v_endPos_2643_);
lean_inc(v_startPos_2624_);
lean_inc_ref(v_inputString_2642_);
v___x_2657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2657_, 0, v_inputString_2642_);
lean_ctor_set(v___x_2657_, 1, v_startPos_2624_);
lean_ctor_set(v___x_2657_, 2, v_endPos_2643_);
v___y_2653_ = v___x_2657_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2658_; 
lean_inc(v_pos_2630_);
lean_inc(v_startPos_2624_);
lean_inc_ref(v_inputString_2642_);
v___x_2658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2658_, 0, v_inputString_2642_);
lean_ctor_set(v___x_2658_, 1, v_startPos_2624_);
lean_ctor_set(v___x_2658_, 2, v_pos_2630_);
v___y_2653_ = v___x_2658_;
goto v___jp_2652_;
}
v___jp_2644_:
{
lean_object* v_leading_2648_; uint8_t v___x_2649_; 
lean_inc(v_startPos_2624_);
v_leading_2648_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2628_, v_startPos_2624_);
lean_dec_ref(v_c_2628_);
v___x_2649_ = lean_nat_dec_le(v_pos_2647_, v_endPos_2643_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
lean_dec(v_pos_2647_);
lean_inc(v_pos_2630_);
v___x_2650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2650_, 0, v_inputString_2642_);
lean_ctor_set(v___x_2650_, 1, v_pos_2630_);
lean_ctor_set(v___x_2650_, 2, v_endPos_2643_);
v___y_2632_ = v_leading_2648_;
v___y_2633_ = v___y_2646_;
v___y_2634_ = v___y_2645_;
v___y_2635_ = v___x_2650_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2651_; 
lean_dec(v_endPos_2643_);
lean_inc(v_pos_2630_);
v___x_2651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2651_, 0, v_inputString_2642_);
lean_ctor_set(v___x_2651_, 1, v_pos_2630_);
lean_ctor_set(v___x_2651_, 2, v_pos_2647_);
v___y_2632_ = v_leading_2648_;
v___y_2633_ = v___y_2646_;
v___y_2634_ = v___y_2645_;
v___y_2635_ = v___x_2651_;
goto v___jp_2631_;
}
}
v___jp_2652_:
{
if (v_includeWhitespace_2627_ == 0)
{
lean_inc(v_pos_2630_);
v___y_2645_ = v___y_2653_;
v___y_2646_ = v_s_2629_;
v_pos_2647_ = v_pos_2630_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2654_; lean_object* v_pos_2655_; 
lean_inc_ref(v_c_2628_);
v___x_2654_ = l_Lean_Parser_whitespace(v_c_2628_, v_s_2629_);
v_pos_2655_ = lean_ctor_get(v___x_2654_, 2);
lean_inc(v_pos_2655_);
v___y_2645_ = v___y_2653_;
v___y_2646_ = v___x_2654_;
v_pos_2647_ = v_pos_2655_;
goto v___jp_2644_;
}
}
}
else
{
lean_object* v___x_2659_; 
lean_dec(v_val_2626_);
v___x_2659_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2624_, v_tk_2625_, v_c_2628_, v_s_2629_);
return v___x_2659_;
}
v___jp_2631_:
{
lean_object* v_info_2636_; lean_object* v___x_2637_; lean_object* v_atom_2638_; lean_object* v___x_2639_; 
v_info_2636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2636_, 0, v___y_2632_);
lean_ctor_set(v_info_2636_, 1, v_startPos_2624_);
lean_ctor_set(v_info_2636_, 2, v___y_2635_);
lean_ctor_set(v_info_2636_, 3, v_pos_2630_);
v___x_2637_ = lean_box(0);
v_atom_2638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2638_, 0, v_info_2636_);
lean_ctor_set(v_atom_2638_, 1, v___y_2634_);
lean_ctor_set(v_atom_2638_, 2, v_val_2626_);
lean_ctor_set(v_atom_2638_, 3, v___x_2637_);
v___x_2639_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2633_, v_atom_2638_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2660_, lean_object* v_tk_2661_, lean_object* v_val_2662_, lean_object* v_includeWhitespace_2663_, lean_object* v_c_2664_, lean_object* v_s_2665_){
_start:
{
uint8_t v_includeWhitespace_boxed_2666_; lean_object* v_res_2667_; 
v_includeWhitespace_boxed_2666_ = lean_unbox(v_includeWhitespace_2663_);
v_res_2667_ = l_Lean_Parser_mkIdResult(v_startPos_2660_, v_tk_2661_, v_val_2662_, v_includeWhitespace_boxed_2666_, v_c_2664_, v_s_2665_);
lean_dec(v_tk_2661_);
return v_res_2667_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2668_){
_start:
{
uint8_t v___y_2670_; uint8_t v___y_2682_; uint32_t v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = 65;
v___x_2693_ = lean_uint32_dec_le(v___x_2692_, v___y_2668_);
if (v___x_2693_ == 0)
{
goto v___jp_2687_;
}
else
{
uint32_t v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = 90;
v___x_2695_ = lean_uint32_dec_le(v___y_2668_, v___x_2694_);
if (v___x_2695_ == 0)
{
goto v___jp_2687_;
}
else
{
return v___x_2695_;
}
}
v___jp_2669_:
{
if (v___y_2670_ == 0)
{
uint32_t v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = 95;
v___x_2672_ = lean_uint32_dec_eq(v___y_2668_, v___x_2671_);
if (v___x_2672_ == 0)
{
uint32_t v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = 39;
v___x_2674_ = lean_uint32_dec_eq(v___y_2668_, v___x_2673_);
if (v___x_2674_ == 0)
{
uint32_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = 33;
v___x_2676_ = lean_uint32_dec_eq(v___y_2668_, v___x_2675_);
if (v___x_2676_ == 0)
{
uint32_t v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = 63;
v___x_2678_ = lean_uint32_dec_eq(v___y_2668_, v___x_2677_);
if (v___x_2678_ == 0)
{
uint8_t v___x_2679_; 
v___x_2679_ = l_Lean_isLetterLike(v___y_2668_);
if (v___x_2679_ == 0)
{
uint8_t v___x_2680_; 
v___x_2680_ = l_Lean_isSubScriptAlnum(v___y_2668_);
return v___x_2680_;
}
else
{
return v___x_2679_;
}
}
else
{
return v___x_2678_;
}
}
else
{
return v___x_2676_;
}
}
else
{
return v___x_2674_;
}
}
else
{
return v___x_2672_;
}
}
else
{
return v___y_2670_;
}
}
v___jp_2681_:
{
if (v___y_2682_ == 0)
{
uint32_t v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = 48;
v___x_2684_ = lean_uint32_dec_le(v___x_2683_, v___y_2668_);
if (v___x_2684_ == 0)
{
v___y_2670_ = v___x_2684_;
goto v___jp_2669_;
}
else
{
uint32_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = 57;
v___x_2686_ = lean_uint32_dec_le(v___y_2668_, v___x_2685_);
v___y_2670_ = v___x_2686_;
goto v___jp_2669_;
}
}
else
{
return v___y_2682_;
}
}
v___jp_2687_:
{
uint32_t v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = 97;
v___x_2689_ = lean_uint32_dec_le(v___x_2688_, v___y_2668_);
if (v___x_2689_ == 0)
{
v___y_2682_ = v___x_2689_;
goto v___jp_2681_;
}
else
{
uint32_t v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = 122;
v___x_2691_ = lean_uint32_dec_le(v___y_2668_, v___x_2690_);
v___y_2682_ = v___x_2691_;
goto v___jp_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2696_){
_start:
{
uint32_t v___y_633__boxed_2697_; uint8_t v_res_2698_; lean_object* v_r_2699_; 
v___y_633__boxed_2697_ = lean_unbox_uint32(v___y_2696_);
lean_dec(v___y_2696_);
v_res_2698_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_633__boxed_2697_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2700_){
_start:
{
uint32_t v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = 187;
v___x_2702_ = lean_uint32_dec_eq(v___y_2700_, v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2703_){
_start:
{
uint32_t v___y_690__boxed_2704_; uint8_t v_res_2705_; lean_object* v_r_2706_; 
v___y_690__boxed_2704_ = lean_unbox_uint32(v___y_2703_);
lean_dec(v___y_2703_);
v_res_2705_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_690__boxed_2704_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2710_, lean_object* v_tk_2711_, uint8_t v_includeWhitespace_2712_, lean_object* v_r_2713_, lean_object* v_c_2714_, lean_object* v_s_2715_){
_start:
{
lean_object* v_pos_2716_; lean_object* v_toInputContext_2717_; uint8_t v___x_2718_; 
v_pos_2716_ = lean_ctor_get(v_s_2715_, 2);
v_toInputContext_2717_ = lean_ctor_get(v_c_2714_, 0);
v___x_2718_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2717_, v_pos_2716_);
if (v___x_2718_ == 0)
{
lean_object* v_inputString_2719_; uint32_t v_curr_2720_; uint32_t v___x_2721_; uint8_t v___x_2722_; 
v_inputString_2719_ = lean_ctor_get(v_toInputContext_2717_, 0);
v_curr_2720_ = lean_string_utf8_get_fast(v_inputString_2719_, v_pos_2716_);
v___x_2721_ = 171;
v___x_2722_ = lean_uint32_dec_eq(v_curr_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___f_2723_; uint8_t v___y_2735_; uint8_t v___y_2738_; uint32_t v___x_2747_; uint8_t v___x_2748_; 
v___f_2723_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2747_ = 65;
v___x_2748_ = lean_uint32_dec_le(v___x_2747_, v_curr_2720_);
if (v___x_2748_ == 0)
{
goto v___jp_2742_;
}
else
{
uint32_t v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = 90;
v___x_2750_ = lean_uint32_dec_le(v_curr_2720_, v___x_2749_);
if (v___x_2750_ == 0)
{
goto v___jp_2742_;
}
else
{
lean_inc(v_pos_2716_);
goto v___jp_2724_;
}
}
v___jp_2724_:
{
lean_object* v___x_2725_; lean_object* v_s_2726_; lean_object* v_pos_2727_; lean_object* v___x_2728_; lean_object* v_r_2729_; uint8_t v___x_2730_; 
v___x_2725_ = l_Lean_Parser_ParserState_next(v_s_2715_, v_c_2714_, v_pos_2716_);
v_s_2726_ = l_Lean_Parser_takeWhileFn(v___f_2723_, v_c_2714_, v___x_2725_);
v_pos_2727_ = lean_ctor_get(v_s_2726_, 2);
lean_inc(v_pos_2727_);
v___x_2728_ = lean_string_utf8_extract(v_inputString_2719_, v_pos_2716_, v_pos_2727_);
lean_dec(v_pos_2716_);
v_r_2729_ = l_Lean_Name_str___override(v_r_2713_, v___x_2728_);
v___x_2730_ = l_Lean_Parser_isIdCont(v_c_2714_, v_s_2726_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v_pos_2727_);
v___x_2731_ = l_Lean_Parser_mkIdResult(v_startPos_2710_, v_tk_2711_, v_r_2729_, v_includeWhitespace_2712_, v_c_2714_, v_s_2726_);
return v___x_2731_;
}
else
{
lean_object* v_s_2732_; 
v_s_2732_ = l_Lean_Parser_ParserState_next(v_s_2726_, v_c_2714_, v_pos_2727_);
lean_dec(v_pos_2727_);
v_r_2713_ = v_r_2729_;
v_s_2715_ = v_s_2732_;
goto _start;
}
}
v___jp_2734_:
{
if (v___y_2735_ == 0)
{
lean_object* v___x_2736_; 
lean_dec(v_r_2713_);
v___x_2736_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2710_, v_tk_2711_, v_c_2714_, v_s_2715_);
return v___x_2736_;
}
else
{
lean_inc(v_pos_2716_);
goto v___jp_2724_;
}
}
v___jp_2737_:
{
if (v___y_2738_ == 0)
{
uint32_t v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = 95;
v___x_2740_ = lean_uint32_dec_eq(v_curr_2720_, v___x_2739_);
if (v___x_2740_ == 0)
{
uint8_t v___x_2741_; 
v___x_2741_ = l_Lean_isLetterLike(v_curr_2720_);
v___y_2735_ = v___x_2741_;
goto v___jp_2734_;
}
else
{
v___y_2735_ = v___x_2740_;
goto v___jp_2734_;
}
}
else
{
lean_inc(v_pos_2716_);
goto v___jp_2724_;
}
}
v___jp_2742_:
{
uint32_t v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = 97;
v___x_2744_ = lean_uint32_dec_le(v___x_2743_, v_curr_2720_);
if (v___x_2744_ == 0)
{
v___y_2738_ = v___x_2744_;
goto v___jp_2737_;
}
else
{
uint32_t v___x_2745_; uint8_t v___x_2746_; 
v___x_2745_ = 122;
v___x_2746_ = lean_uint32_dec_le(v_curr_2720_, v___x_2745_);
v___y_2738_ = v___x_2746_;
goto v___jp_2737_;
}
}
}
else
{
lean_object* v___f_2751_; lean_object* v_startPart_2752_; lean_object* v___x_2753_; lean_object* v_s_2754_; lean_object* v_pos_2755_; uint8_t v___x_2756_; 
v___f_2751_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2752_ = lean_string_utf8_next_fast(v_inputString_2719_, v_pos_2716_);
v___x_2753_ = l_Lean_Parser_ParserState_setPos(v_s_2715_, v_startPart_2752_);
v_s_2754_ = l_Lean_Parser_takeUntilFn(v___f_2751_, v_c_2714_, v___x_2753_);
v_pos_2755_ = lean_ctor_get(v_s_2754_, 2);
lean_inc(v_pos_2755_);
v___x_2756_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2717_, v_pos_2755_);
if (v___x_2756_ == 0)
{
lean_object* v_s_2757_; lean_object* v___x_2758_; lean_object* v_r_2759_; uint8_t v___x_2760_; 
v_s_2757_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2754_, v_c_2714_, v_pos_2755_);
v___x_2758_ = lean_string_utf8_extract(v_inputString_2719_, v_startPart_2752_, v_pos_2755_);
lean_dec(v_pos_2755_);
v_r_2759_ = l_Lean_Name_str___override(v_r_2713_, v___x_2758_);
v___x_2760_ = l_Lean_Parser_isIdCont(v_c_2714_, v_s_2757_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Parser_mkIdResult(v_startPos_2710_, v_tk_2711_, v_r_2759_, v_includeWhitespace_2712_, v_c_2714_, v_s_2757_);
return v___x_2761_;
}
else
{
lean_object* v_pos_2762_; lean_object* v_s_2763_; 
v_pos_2762_ = lean_ctor_get(v_s_2757_, 2);
lean_inc(v_pos_2762_);
v_s_2763_ = l_Lean_Parser_ParserState_next(v_s_2757_, v_c_2714_, v_pos_2762_);
lean_dec(v_pos_2762_);
v_r_2713_ = v_r_2759_;
v_s_2715_ = v_s_2763_;
goto _start;
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec(v_pos_2755_);
lean_dec_ref(v_c_2714_);
lean_dec(v_r_2713_);
lean_dec(v_startPos_2710_);
v___x_2765_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2766_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2754_, v___x_2765_, v_startPart_2752_);
return v___x_2766_;
}
}
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec_ref(v_c_2714_);
lean_dec(v_r_2713_);
lean_dec(v_startPos_2710_);
v___x_2767_ = lean_box(0);
v___x_2768_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2715_, v___x_2767_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2769_, lean_object* v_tk_2770_, lean_object* v_includeWhitespace_2771_, lean_object* v_r_2772_, lean_object* v_c_2773_, lean_object* v_s_2774_){
_start:
{
uint8_t v_includeWhitespace_boxed_2775_; lean_object* v_res_2776_; 
v_includeWhitespace_boxed_2775_ = lean_unbox(v_includeWhitespace_2771_);
v_res_2776_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2769_, v_tk_2770_, v_includeWhitespace_boxed_2775_, v_r_2772_, v_c_2773_, v_s_2774_);
lean_dec(v_tk_2770_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2777_, lean_object* v_tk_2778_, lean_object* v_r_2779_, uint8_t v_includeWhitespace_2780_, lean_object* v_c_2781_, lean_object* v_s_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2777_, v_tk_2778_, v_includeWhitespace_2780_, v_r_2779_, v_c_2781_, v_s_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2784_, lean_object* v_tk_2785_, lean_object* v_r_2786_, lean_object* v_includeWhitespace_2787_, lean_object* v_c_2788_, lean_object* v_s_2789_){
_start:
{
uint8_t v_includeWhitespace_boxed_2790_; lean_object* v_res_2791_; 
v_includeWhitespace_boxed_2790_ = lean_unbox(v_includeWhitespace_2787_);
v_res_2791_ = l_Lean_Parser_identFnAux(v_startPos_2784_, v_tk_2785_, v_r_2786_, v_includeWhitespace_boxed_2790_, v_c_2788_, v_s_2789_);
lean_dec(v_tk_2785_);
return v_res_2791_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2792_){
_start:
{
uint8_t v___y_2794_; uint8_t v___y_2798_; uint32_t v___x_2807_; uint8_t v___x_2808_; 
v___x_2807_ = 65;
v___x_2808_ = lean_uint32_dec_le(v___x_2807_, v_c_2792_);
if (v___x_2808_ == 0)
{
goto v___jp_2802_;
}
else
{
uint32_t v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = 90;
v___x_2810_ = lean_uint32_dec_le(v_c_2792_, v___x_2809_);
if (v___x_2810_ == 0)
{
goto v___jp_2802_;
}
else
{
return v___x_2810_;
}
}
v___jp_2793_:
{
if (v___y_2794_ == 0)
{
uint32_t v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = 171;
v___x_2796_ = lean_uint32_dec_eq(v_c_2792_, v___x_2795_);
return v___x_2796_;
}
else
{
return v___y_2794_;
}
}
v___jp_2797_:
{
if (v___y_2798_ == 0)
{
uint32_t v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = 95;
v___x_2800_ = lean_uint32_dec_eq(v_c_2792_, v___x_2799_);
if (v___x_2800_ == 0)
{
uint8_t v___x_2801_; 
v___x_2801_ = l_Lean_isLetterLike(v_c_2792_);
v___y_2794_ = v___x_2801_;
goto v___jp_2793_;
}
else
{
v___y_2794_ = v___x_2800_;
goto v___jp_2793_;
}
}
else
{
return v___y_2798_;
}
}
v___jp_2802_:
{
uint32_t v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = 97;
v___x_2804_ = lean_uint32_dec_le(v___x_2803_, v_c_2792_);
if (v___x_2804_ == 0)
{
v___y_2798_ = v___x_2804_;
goto v___jp_2797_;
}
else
{
uint32_t v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = 122;
v___x_2806_ = lean_uint32_dec_le(v_c_2792_, v___x_2805_);
v___y_2798_ = v___x_2806_;
goto v___jp_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2811_){
_start:
{
uint32_t v_c_boxed_2812_; uint8_t v_res_2813_; lean_object* v_r_2814_; 
v_c_boxed_2812_ = lean_unbox_uint32(v_c_2811_);
lean_dec(v_c_2811_);
v_res_2813_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2812_);
v_r_2814_ = lean_box(v_res_2813_);
return v_r_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2816_, lean_object* v_c_2817_, lean_object* v_s_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; lean_object* v___x_2822_; lean_object* v_s_2823_; lean_object* v_stxStack_2824_; lean_object* v_errorMsg_2825_; uint8_t v___x_2826_; 
v___x_2819_ = lean_box(0);
v___x_2820_ = lean_box(0);
v___x_2821_ = 1;
v___x_2822_ = l_Lean_Parser_ParserState_next(v_s_2818_, v_c_2817_, v_startPos_2816_);
v_s_2823_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2816_, v___x_2819_, v___x_2821_, v___x_2820_, v_c_2817_, v___x_2822_);
v_stxStack_2824_ = lean_ctor_get(v_s_2823_, 0);
lean_inc_ref(v_stxStack_2824_);
v_errorMsg_2825_ = lean_ctor_get(v_s_2823_, 4);
lean_inc(v_errorMsg_2825_);
v___x_2826_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2825_, v___x_2819_);
lean_dec(v_errorMsg_2825_);
if (v___x_2826_ == 0)
{
lean_dec_ref(v_stxStack_2824_);
return v_s_2823_;
}
else
{
lean_object* v_stx_2827_; 
v_stx_2827_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2824_);
lean_dec_ref(v_stxStack_2824_);
if (lean_obj_tag(v_stx_2827_) == 3)
{
lean_object* v_rawVal_2828_; lean_object* v_info_2829_; lean_object* v_str_2830_; lean_object* v_startPos_2831_; lean_object* v_stopPos_2832_; lean_object* v_s_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_rawVal_2828_ = lean_ctor_get(v_stx_2827_, 1);
lean_inc_ref(v_rawVal_2828_);
v_info_2829_ = lean_ctor_get(v_stx_2827_, 0);
lean_inc(v_info_2829_);
lean_dec_ref_known(v_stx_2827_, 4);
v_str_2830_ = lean_ctor_get(v_rawVal_2828_, 0);
lean_inc_ref(v_str_2830_);
v_startPos_2831_ = lean_ctor_get(v_rawVal_2828_, 1);
lean_inc(v_startPos_2831_);
v_stopPos_2832_ = lean_ctor_get(v_rawVal_2828_, 2);
lean_inc(v_stopPos_2832_);
lean_dec_ref(v_rawVal_2828_);
v_s_2833_ = l_Lean_Parser_ParserState_popSyntax(v_s_2823_);
v___x_2834_ = lean_string_utf8_extract(v_str_2830_, v_startPos_2831_, v_stopPos_2832_);
lean_dec(v_stopPos_2832_);
lean_dec(v_startPos_2831_);
lean_dec_ref(v_str_2830_);
v___x_2835_ = l_Lean_Syntax_mkNameLit(v___x_2834_, v_info_2829_);
v___x_2836_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2833_, v___x_2835_);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec(v_stx_2827_);
v___x_2837_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2838_ = l_Lean_Parser_ParserState_mkError(v_s_2823_, v___x_2837_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2839_, lean_object* v_s_2840_){
_start:
{
lean_object* v_toInputContext_2841_; lean_object* v_pos_2842_; lean_object* v_tokens_2843_; lean_object* v_inputString_2844_; lean_object* v_endPos_2845_; uint32_t v_curr_2846_; uint32_t v___x_2847_; uint8_t v___x_2848_; uint8_t v___x_2849_; uint8_t v___y_2851_; uint8_t v___y_2858_; uint8_t v___y_2865_; uint8_t v___y_2873_; 
v_toInputContext_2841_ = lean_ctor_get(v_c_2839_, 0);
v_pos_2842_ = lean_ctor_get(v_s_2840_, 2);
v_tokens_2843_ = lean_ctor_get(v_c_2839_, 3);
v_inputString_2844_ = lean_ctor_get(v_toInputContext_2841_, 0);
v_endPos_2845_ = lean_ctor_get(v_toInputContext_2841_, 3);
v_curr_2846_ = lean_string_utf8_get(v_inputString_2844_, v_pos_2842_);
v___x_2847_ = 34;
v___x_2848_ = lean_uint32_dec_eq(v_curr_2846_, v___x_2847_);
v___x_2849_ = 1;
if (v___x_2848_ == 0)
{
uint32_t v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = 39;
v___x_2881_ = lean_uint32_dec_eq(v_curr_2846_, v___x_2880_);
if (v___x_2881_ == 0)
{
v___y_2873_ = v___x_2881_;
goto v___jp_2872_;
}
else
{
lean_object* v___x_2882_; uint32_t v___x_2883_; uint8_t v___x_2884_; 
v___x_2882_ = lean_string_utf8_next(v_inputString_2844_, v_pos_2842_);
v___x_2883_ = lean_string_utf8_get(v_inputString_2844_, v___x_2882_);
lean_dec(v___x_2882_);
v___x_2884_ = lean_uint32_dec_eq(v___x_2883_, v___x_2880_);
if (v___x_2884_ == 0)
{
v___y_2873_ = v___x_2881_;
goto v___jp_2872_;
}
else
{
v___y_2873_ = v___x_2848_;
goto v___jp_2872_;
}
}
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_inc(v_pos_2842_);
v___x_2885_ = l_Lean_Parser_ParserState_next(v_s_2840_, v_c_2839_, v_pos_2842_);
v___x_2886_ = l_Lean_Parser_strLitFnAux(v_pos_2842_, v___x_2849_, v_c_2839_, v___x_2885_);
return v___x_2886_;
}
v___jp_2850_:
{
if (v___y_2851_ == 0)
{
lean_object* v_tk_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_inc(v_pos_2842_);
v_tk_2852_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2844_, v_tokens_2843_, v_pos_2842_, v_endPos_2845_);
v___x_2853_ = lean_box(0);
v___x_2854_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2842_, v_tk_2852_, v___x_2849_, v___x_2853_, v_c_2839_, v_s_2840_);
lean_dec(v_tk_2852_);
return v___x_2854_;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = l_Lean_Parser_ParserState_next(v_s_2840_, v_c_2839_, v_pos_2842_);
v___x_2856_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2842_, v_c_2839_, v___x_2855_);
return v___x_2856_;
}
}
v___jp_2857_:
{
if (v___y_2858_ == 0)
{
uint32_t v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = 114;
v___x_2860_ = lean_uint32_dec_eq(v_curr_2846_, v___x_2859_);
if (v___x_2860_ == 0)
{
v___y_2851_ = v___x_2860_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = lean_string_utf8_next(v_inputString_2844_, v_pos_2842_);
v___x_2862_ = l_Lean_Parser_isRawStrLitStart(v_c_2839_, v___x_2861_);
v___y_2851_ = v___x_2862_;
goto v___jp_2850_;
}
}
else
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2842_, v_c_2839_, v_s_2840_);
return v___x_2863_;
}
}
v___jp_2864_:
{
if (v___y_2865_ == 0)
{
uint32_t v___x_2866_; uint8_t v___x_2867_; 
lean_inc(v_pos_2842_);
v___x_2866_ = 96;
v___x_2867_ = lean_uint32_dec_eq(v_curr_2846_, v___x_2866_);
if (v___x_2867_ == 0)
{
v___y_2858_ = v___x_2867_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2868_; uint32_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = lean_string_utf8_next(v_inputString_2844_, v_pos_2842_);
v___x_2869_ = lean_string_utf8_get(v_inputString_2844_, v___x_2868_);
lean_dec(v___x_2868_);
v___x_2870_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2869_);
v___y_2858_ = v___x_2870_;
goto v___jp_2857_;
}
}
else
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Parser_numberFnAux(v___x_2849_, v_c_2839_, v_s_2840_);
return v___x_2871_;
}
}
v___jp_2872_:
{
if (v___y_2873_ == 0)
{
uint32_t v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = 48;
v___x_2875_ = lean_uint32_dec_le(v___x_2874_, v_curr_2846_);
if (v___x_2875_ == 0)
{
v___y_2865_ = v___x_2875_;
goto v___jp_2864_;
}
else
{
uint32_t v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = 57;
v___x_2877_ = lean_uint32_dec_le(v_curr_2846_, v___x_2876_);
v___y_2865_ = v___x_2877_;
goto v___jp_2864_;
}
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_inc(v_pos_2842_);
v___x_2878_ = l_Lean_Parser_ParserState_next(v_s_2840_, v_c_2839_, v_pos_2842_);
v___x_2879_ = l_Lean_Parser_charLitFnAux(v_pos_2842_, v_c_2839_, v___x_2878_);
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2887_, lean_object* v_s_2888_){
_start:
{
lean_object* v_cache_2889_; lean_object* v_errorMsg_2890_; 
v_cache_2889_ = lean_ctor_get(v_s_2888_, 3);
lean_inc_ref(v_cache_2889_);
v_errorMsg_2890_ = lean_ctor_get(v_s_2888_, 4);
if (lean_obj_tag(v_errorMsg_2890_) == 0)
{
lean_object* v_stxStack_2891_; lean_object* v_lhsPrec_2892_; lean_object* v_pos_2893_; lean_object* v_recoveredErrors_2894_; lean_object* v_parserCache_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2920_; 
v_stxStack_2891_ = lean_ctor_get(v_s_2888_, 0);
v_lhsPrec_2892_ = lean_ctor_get(v_s_2888_, 1);
v_pos_2893_ = lean_ctor_get(v_s_2888_, 2);
v_recoveredErrors_2894_ = lean_ctor_get(v_s_2888_, 5);
v_parserCache_2895_ = lean_ctor_get(v_cache_2889_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_cache_2889_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v_cache_2889_, 0);
lean_dec(v_unused_2921_);
v___x_2897_ = v_cache_2889_;
v_isShared_2898_ = v_isSharedCheck_2920_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_parserCache_2895_);
lean_dec(v_cache_2889_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2920_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2899_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2891_);
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = lean_nat_dec_eq(v___x_2899_, v___x_2900_);
lean_dec(v___x_2899_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2913_; 
lean_inc_ref(v_recoveredErrors_2894_);
lean_inc(v_pos_2893_);
lean_inc(v_lhsPrec_2892_);
lean_inc_ref(v_stxStack_2891_);
lean_inc(v_errorMsg_2890_);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_s_2888_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; lean_object* v_unused_2919_; 
v_unused_2914_ = lean_ctor_get(v_s_2888_, 5);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_s_2888_, 4);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_s_2888_, 3);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_s_2888_, 2);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_s_2888_, 1);
lean_dec(v_unused_2918_);
v_unused_2919_ = lean_ctor_get(v_s_2888_, 0);
lean_dec(v_unused_2919_);
v___x_2903_ = v_s_2888_;
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v_s_2888_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_tk_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v_tk_2905_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2891_);
lean_inc(v_pos_2893_);
v___x_2906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2906_, 0, v_startPos_2887_);
lean_ctor_set(v___x_2906_, 1, v_pos_2893_);
lean_ctor_set(v___x_2906_, 2, v_tk_2905_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2906_);
v___x_2908_ = v___x_2897_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_parserCache_2895_);
v___x_2908_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2910_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 3, v___x_2908_);
v___x_2910_ = v___x_2903_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_stxStack_2891_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_lhsPrec_2892_);
lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_pos_2893_);
lean_ctor_set(v_reuseFailAlloc_2911_, 3, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_errorMsg_2890_);
lean_ctor_set(v_reuseFailAlloc_2911_, 5, v_recoveredErrors_2894_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_del_object(v___x_2897_);
lean_dec_ref(v_parserCache_2895_);
lean_dec(v_startPos_2887_);
return v_s_2888_;
}
}
}
else
{
lean_dec_ref(v_cache_2889_);
lean_dec(v_startPos_2887_);
return v_s_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2922_, lean_object* v_c_2923_, lean_object* v_s_2924_){
_start:
{
lean_object* v_pos_2925_; lean_object* v_cache_2926_; lean_object* v_toInputContext_2927_; uint8_t v___x_2928_; 
v_pos_2925_ = lean_ctor_get(v_s_2924_, 2);
v_cache_2926_ = lean_ctor_get(v_s_2924_, 3);
v_toInputContext_2927_ = lean_ctor_get(v_c_2923_, 0);
v___x_2928_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2927_, v_pos_2925_);
if (v___x_2928_ == 0)
{
lean_object* v_tokenCache_2929_; lean_object* v_startPos_2930_; lean_object* v_stopPos_2931_; lean_object* v_token_2932_; uint8_t v___x_2933_; 
lean_dec(v_expected_2922_);
v_tokenCache_2929_ = lean_ctor_get(v_cache_2926_, 0);
v_startPos_2930_ = lean_ctor_get(v_tokenCache_2929_, 0);
v_stopPos_2931_ = lean_ctor_get(v_tokenCache_2929_, 1);
v_token_2932_ = lean_ctor_get(v_tokenCache_2929_, 2);
v___x_2933_ = lean_nat_dec_eq(v_startPos_2930_, v_pos_2925_);
if (v___x_2933_ == 0)
{
lean_object* v_s_2934_; lean_object* v___x_2935_; 
lean_inc(v_pos_2925_);
v_s_2934_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2923_, v_s_2924_);
v___x_2935_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2925_, v_s_2934_);
return v___x_2935_;
}
else
{
lean_object* v_s_2936_; lean_object* v___x_2937_; 
lean_inc(v_token_2932_);
lean_inc(v_stopPos_2931_);
lean_dec_ref(v_c_2923_);
v_s_2936_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2924_, v_token_2932_);
v___x_2937_ = l_Lean_Parser_ParserState_setPos(v_s_2936_, v_stopPos_2931_);
return v___x_2937_;
}
}
else
{
lean_object* v___x_2938_; 
lean_dec_ref(v_c_2923_);
v___x_2938_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2924_, v_expected_2922_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2939_, lean_object* v_s_2940_){
_start:
{
lean_object* v_pos_2941_; lean_object* v_iniSz_2942_; lean_object* v___x_2943_; lean_object* v_s_2944_; lean_object* v_errorMsg_2945_; 
v_pos_2941_ = lean_ctor_get(v_s_2940_, 2);
lean_inc(v_pos_2941_);
v_iniSz_2942_ = l_Lean_Parser_ParserState_stackSize(v_s_2940_);
v___x_2943_ = lean_box(0);
v_s_2944_ = l_Lean_Parser_tokenFn(v___x_2943_, v_c_2939_, v_s_2940_);
v_errorMsg_2945_ = lean_ctor_get(v_s_2944_, 4);
lean_inc(v_errorMsg_2945_);
if (lean_obj_tag(v_errorMsg_2945_) == 1)
{
lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2954_; 
v_isSharedCheck_2954_ = !lean_is_exclusive(v_errorMsg_2945_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v_errorMsg_2945_, 0);
lean_dec(v_unused_2955_);
v___x_2947_ = v_errorMsg_2945_;
v_isShared_2948_ = v_isSharedCheck_2954_;
goto v_resetjp_2946_;
}
else
{
lean_dec(v_errorMsg_2945_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2954_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
lean_inc_ref(v_s_2944_);
v___x_2949_ = l_Lean_Parser_ParserState_restore(v_s_2944_, v_iniSz_2942_, v_pos_2941_);
lean_dec(v_iniSz_2942_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 0);
lean_ctor_set(v___x_2947_, 0, v_s_2944_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_s_2944_);
v___x_2951_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2949_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
return v___x_2952_;
}
}
}
else
{
lean_object* v_stxStack_2956_; lean_object* v_stx_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v_errorMsg_2945_);
v_stxStack_2956_ = lean_ctor_get(v_s_2944_, 0);
lean_inc_ref(v_stxStack_2956_);
v_stx_2957_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2956_);
lean_dec_ref(v_stxStack_2956_);
v___x_2958_ = l_Lean_Parser_ParserState_restore(v_s_2944_, v_iniSz_2942_, v_pos_2941_);
lean_dec(v_iniSz_2942_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v_stx_2957_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2961_, lean_object* v_s_2962_){
_start:
{
lean_object* v_cache_2963_; lean_object* v_tokenCache_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2977_; 
v_cache_2963_ = lean_ctor_get(v_s_2962_, 3);
lean_inc_ref(v_cache_2963_);
v_tokenCache_2964_ = lean_ctor_get(v_cache_2963_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_cache_2963_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v_cache_2963_, 1);
lean_dec(v_unused_2978_);
v___x_2966_ = v_cache_2963_;
v_isShared_2967_ = v_isSharedCheck_2977_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_tokenCache_2964_);
lean_dec(v_cache_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2977_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_pos_2968_; lean_object* v_startPos_2969_; lean_object* v_token_2970_; uint8_t v___x_2971_; 
v_pos_2968_ = lean_ctor_get(v_s_2962_, 2);
v_startPos_2969_ = lean_ctor_get(v_tokenCache_2964_, 0);
lean_inc(v_startPos_2969_);
v_token_2970_ = lean_ctor_get(v_tokenCache_2964_, 2);
lean_inc(v_token_2970_);
lean_dec_ref(v_tokenCache_2964_);
v___x_2971_ = lean_nat_dec_eq(v_startPos_2969_, v_pos_2968_);
lean_dec(v_startPos_2969_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
lean_dec(v_token_2970_);
lean_del_object(v___x_2966_);
v___x_2972_ = l_Lean_Parser_peekTokenAux(v_c_2961_, v_s_2962_);
return v___x_2972_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_dec_ref(v_c_2961_);
v___x_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_token_2970_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2973_);
lean_ctor_set(v___x_2966_, 0, v_s_2962_);
v___x_2975_ = v___x_2966_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_s_2962_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2979_, lean_object* v_c_2980_, lean_object* v_s_2981_){
_start:
{
lean_object* v_pos_2982_; lean_object* v_toInputContext_2983_; uint8_t v___x_2984_; 
v_pos_2982_ = lean_ctor_get(v_s_2981_, 2);
v_toInputContext_2983_ = lean_ctor_get(v_c_2980_, 0);
v___x_2984_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2983_, v_pos_2982_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_inc(v_pos_2982_);
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_box(0);
v___x_2987_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2982_, v___x_2985_, v_includeWhitespace_2979_, v___x_2986_, v_c_2980_, v_s_2981_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v_c_2980_);
v___x_2988_ = lean_box(0);
v___x_2989_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2981_, v___x_2988_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2990_, lean_object* v_c_2991_, lean_object* v_s_2992_){
_start:
{
uint8_t v_includeWhitespace_boxed_2993_; lean_object* v_res_2994_; 
v_includeWhitespace_boxed_2993_ = lean_unbox(v_includeWhitespace_2990_);
v_res_2994_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2993_, v_c_2991_, v_s_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_2995_, lean_object* v_expected_2996_, lean_object* v_c_2997_, lean_object* v_s_2998_){
_start:
{
lean_object* v_pos_2999_; lean_object* v_s_3000_; lean_object* v_stxStack_3001_; lean_object* v_errorMsg_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v_pos_2999_ = lean_ctor_get(v_s_2998_, 2);
lean_inc(v_pos_2999_);
lean_inc(v_expected_2996_);
v_s_3000_ = l_Lean_Parser_tokenFn(v_expected_2996_, v_c_2997_, v_s_2998_);
v_stxStack_3001_ = lean_ctor_get(v_s_3000_, 0);
lean_inc_ref(v_stxStack_3001_);
v_errorMsg_3002_ = lean_ctor_get(v_s_3000_, 4);
lean_inc(v_errorMsg_3002_);
v___x_3003_ = lean_box(0);
v___x_3004_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3002_, v___x_3003_);
lean_dec(v_errorMsg_3002_);
if (v___x_3004_ == 0)
{
lean_dec_ref(v_stxStack_3001_);
lean_dec(v_pos_2999_);
lean_dec(v_expected_2996_);
lean_dec_ref(v_p_2995_);
return v_s_3000_;
}
else
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3001_);
lean_dec_ref(v_stxStack_3001_);
if (lean_obj_tag(v___x_3005_) == 2)
{
lean_object* v_val_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_val_3006_ = lean_ctor_get(v___x_3005_, 1);
lean_inc_ref(v_val_3006_);
lean_dec_ref_known(v___x_3005_, 2);
v___x_3007_ = lean_apply_1(v_p_2995_, v_val_3006_);
v___x_3008_ = lean_unbox(v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3000_, v_expected_2996_, v_pos_2999_);
return v___x_3009_;
}
else
{
lean_dec(v_pos_2999_);
lean_dec(v_expected_2996_);
return v_s_3000_;
}
}
else
{
lean_object* v___x_3010_; 
lean_dec(v___x_3005_);
lean_dec_ref(v_p_2995_);
v___x_3010_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3000_, v_expected_2996_, v_pos_2999_);
return v___x_3010_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_3011_, lean_object* v_s_3012_){
_start:
{
uint8_t v___x_3013_; 
v___x_3013_ = lean_string_dec_eq(v_s_3012_, v_sym_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_3014_, lean_object* v_s_3015_){
_start:
{
uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_res_3016_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_3014_, v_s_3015_);
lean_dec_ref(v_s_3015_);
lean_dec_ref(v_sym_3014_);
v_r_3017_ = lean_box(v_res_3016_);
return v_r_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_3018_, lean_object* v_errorMsg_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3022_, 0, v_sym_3018_);
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v_errorMsg_3019_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Lean_Parser_satisfySymbolFn(v___f_3022_, v___x_3024_, v_a_3020_, v_a_3021_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_3026_, lean_object* v_tks_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3028_, 0, v_sym_3026_);
lean_ctor_set(v___x_3028_, 1, v_tks_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_3029_){
_start:
{
lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_inc_ref(v_sym_3029_);
v___f_3030_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3030_, 0, v_sym_3029_);
v___f_3031_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_sym_3029_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___f_3030_);
lean_ctor_set(v___x_3035_, 1, v___f_3031_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3039_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3040_ = lean_string_append(v___x_3039_, v_sym_3036_);
v___x_3041_ = lean_string_append(v___x_3040_, v___x_3039_);
v___x_3042_ = l_Lean_Parser_symbolFnAux(v_sym_3036_, v___x_3041_, v_a_3037_, v_a_3038_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_str_3048_; lean_object* v_startInclusive_3049_; lean_object* v_endExclusive_3050_; lean_object* v_sym_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = lean_string_utf8_byte_size(v_sym_3043_);
v___x_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3046_, 0, v_sym_3043_);
lean_ctor_set(v___x_3046_, 1, v___x_3044_);
lean_ctor_set(v___x_3046_, 2, v___x_3045_);
v___x_3047_ = l_String_Slice_trimAscii(v___x_3046_);
v_str_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc_ref(v_str_3048_);
v_startInclusive_3049_ = lean_ctor_get(v___x_3047_, 1);
lean_inc(v_startInclusive_3049_);
v_endExclusive_3050_ = lean_ctor_get(v___x_3047_, 2);
lean_inc(v_endExclusive_3050_);
lean_dec_ref(v___x_3047_);
v_sym_3051_ = lean_string_utf8_extract_fast(v_str_3048_, v_startInclusive_3049_, v_endExclusive_3050_);
lean_dec(v_endExclusive_3050_);
lean_dec(v_startInclusive_3049_);
lean_dec_ref(v_str_3048_);
lean_inc_ref(v_sym_3051_);
v___x_3052_ = l_Lean_Parser_symbolInfo(v_sym_3051_);
v___x_3053_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3053_, 0, v_sym_3051_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3055_, lean_object* v_errorMsg_3056_, lean_object* v_c_3057_, lean_object* v_s_3058_){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_s_3061_; lean_object* v_stxStack_3065_; lean_object* v_errorMsg_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3059_ = lean_box(0);
lean_inc_ref(v_errorMsg_3056_);
v___x_3060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3060_, 0, v_errorMsg_3056_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v_s_3061_ = l_Lean_Parser_tokenFn(v___x_3060_, v_c_3057_, v_s_3058_);
v_stxStack_3065_ = lean_ctor_get(v_s_3061_, 0);
lean_inc_ref(v_stxStack_3065_);
v_errorMsg_3066_ = lean_ctor_get(v_s_3061_, 4);
lean_inc(v_errorMsg_3066_);
v___x_3067_ = lean_box(0);
v___x_3068_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3066_, v___x_3067_);
lean_dec(v_errorMsg_3066_);
if (v___x_3068_ == 0)
{
lean_dec_ref(v_stxStack_3065_);
lean_dec_ref(v_errorMsg_3056_);
lean_dec_ref(v_sym_3055_);
return v_s_3061_;
}
else
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3065_);
lean_dec_ref(v_stxStack_3065_);
switch(lean_obj_tag(v___x_3069_))
{
case 2:
{
lean_object* v_val_3070_; uint8_t v___x_3071_; 
v_val_3070_ = lean_ctor_get(v___x_3069_, 1);
lean_inc_ref(v_val_3070_);
lean_dec_ref_known(v___x_3069_, 2);
v___x_3071_ = lean_string_dec_eq(v_sym_3055_, v_val_3070_);
lean_dec_ref(v_val_3070_);
lean_dec_ref(v_sym_3055_);
if (v___x_3071_ == 0)
{
goto v___jp_3062_;
}
else
{
lean_dec_ref(v_errorMsg_3056_);
return v_s_3061_;
}
}
case 3:
{
lean_object* v_rawVal_3072_; lean_object* v_info_3073_; lean_object* v_str_3074_; lean_object* v_startPos_3075_; lean_object* v_stopPos_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v_rawVal_3072_ = lean_ctor_get(v___x_3069_, 1);
lean_inc_ref(v_rawVal_3072_);
v_info_3073_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_info_3073_);
lean_dec_ref_known(v___x_3069_, 4);
v_str_3074_ = lean_ctor_get(v_rawVal_3072_, 0);
lean_inc_ref(v_str_3074_);
v_startPos_3075_ = lean_ctor_get(v_rawVal_3072_, 1);
lean_inc(v_startPos_3075_);
v_stopPos_3076_ = lean_ctor_get(v_rawVal_3072_, 2);
lean_inc(v_stopPos_3076_);
lean_dec_ref(v_rawVal_3072_);
v___x_3077_ = lean_string_utf8_extract(v_str_3074_, v_startPos_3075_, v_stopPos_3076_);
lean_dec(v_stopPos_3076_);
lean_dec(v_startPos_3075_);
lean_dec_ref(v_str_3074_);
v___x_3078_ = lean_string_dec_eq(v_sym_3055_, v___x_3077_);
lean_dec_ref(v___x_3077_);
if (v___x_3078_ == 0)
{
lean_dec(v_info_3073_);
lean_dec_ref(v_sym_3055_);
goto v___jp_3062_;
}
else
{
lean_object* v_s_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v_errorMsg_3056_);
v_s_3079_ = l_Lean_Parser_ParserState_popSyntax(v_s_3061_);
v___x_3080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3080_, 0, v_info_3073_);
lean_ctor_set(v___x_3080_, 1, v_sym_3055_);
v___x_3081_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3079_, v___x_3080_);
return v___x_3081_;
}
}
default: 
{
lean_dec(v___x_3069_);
lean_dec_ref(v_sym_3055_);
goto v___jp_3062_;
}
}
}
v___jp_3062_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3061_, v_errorMsg_3056_, v___x_3063_);
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3085_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3086_ = lean_string_append(v___x_3085_, v_sym_3082_);
v___x_3087_ = lean_string_append(v___x_3086_, v___x_3085_);
v___x_3088_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3082_, v___x_3087_, v_a_3083_, v_a_3084_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3093_, uint8_t v_includeIdent_3094_){
_start:
{
lean_object* v___f_3095_; lean_object* v___f_3096_; 
v___f_3095_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3096_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3094_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3098_, 0, v_sym_3093_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3100_, 0, v___f_3095_);
lean_ctor_set(v___x_3100_, 1, v___f_3096_);
lean_ctor_set(v___x_3100_, 2, v___x_3099_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3101_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_sym_3093_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3104_, 0, v___f_3095_);
lean_ctor_set(v___x_3104_, 1, v___f_3096_);
lean_ctor_set(v___x_3104_, 2, v___x_3103_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3105_, lean_object* v_includeIdent_3106_){
_start:
{
uint8_t v_includeIdent_boxed_3107_; lean_object* v_res_3108_; 
v_includeIdent_boxed_3107_ = lean_unbox(v_includeIdent_3106_);
v_res_3108_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3105_, v_includeIdent_boxed_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3109_, uint8_t v_includeIdent_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_str_3115_; lean_object* v_startInclusive_3116_; lean_object* v_endExclusive_3117_; lean_object* v_sym_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3111_ = lean_unsigned_to_nat(0u);
v___x_3112_ = lean_string_utf8_byte_size(v_sym_3109_);
v___x_3113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3113_, 0, v_sym_3109_);
lean_ctor_set(v___x_3113_, 1, v___x_3111_);
lean_ctor_set(v___x_3113_, 2, v___x_3112_);
v___x_3114_ = l_String_Slice_trimAscii(v___x_3113_);
v_str_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc_ref(v_str_3115_);
v_startInclusive_3116_ = lean_ctor_get(v___x_3114_, 1);
lean_inc(v_startInclusive_3116_);
v_endExclusive_3117_ = lean_ctor_get(v___x_3114_, 2);
lean_inc(v_endExclusive_3117_);
lean_dec_ref(v___x_3114_);
v_sym_3118_ = lean_string_utf8_extract_fast(v_str_3115_, v_startInclusive_3116_, v_endExclusive_3117_);
lean_dec(v_endExclusive_3117_);
lean_dec(v_startInclusive_3116_);
lean_dec_ref(v_str_3115_);
lean_inc_ref(v_sym_3118_);
v___x_3119_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3118_, v_includeIdent_3110_);
v___x_3120_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3120_, 0, v_sym_3118_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3122_, lean_object* v_includeIdent_3123_){
_start:
{
uint8_t v_includeIdent_boxed_3124_; lean_object* v_res_3125_; 
v_includeIdent_boxed_3124_ = lean_unbox(v_includeIdent_3123_);
v_res_3125_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3122_, v_includeIdent_boxed_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3126_, lean_object* v_errorMsg_3127_, lean_object* v_j_3128_, lean_object* v_c_3129_, lean_object* v_s_3130_){
_start:
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_string_utf8_at_end(v_sym_3126_, v_j_3128_);
if (v___x_3131_ == 0)
{
lean_object* v_pos_3132_; lean_object* v_toInputContext_3133_; uint8_t v___x_3134_; 
v_pos_3132_ = lean_ctor_get(v_s_3130_, 2);
v_toInputContext_3133_ = lean_ctor_get(v_c_3129_, 0);
v___x_3134_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3133_, v_pos_3132_);
if (v___x_3134_ == 0)
{
lean_object* v_inputString_3135_; uint32_t v___x_3136_; uint32_t v___x_3137_; uint8_t v___x_3138_; 
v_inputString_3135_ = lean_ctor_get(v_toInputContext_3133_, 0);
v___x_3136_ = lean_string_utf8_get_fast(v_sym_3126_, v_j_3128_);
v___x_3137_ = lean_string_utf8_get_fast(v_inputString_3135_, v_pos_3132_);
v___x_3138_ = lean_uint32_dec_eq(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_dec(v_j_3128_);
v___x_3139_ = l_Lean_Parser_ParserState_mkError(v_s_3130_, v_errorMsg_3127_);
return v___x_3139_;
}
else
{
if (v___x_3134_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_inc(v_pos_3132_);
v___x_3140_ = lean_string_utf8_next_fast(v_sym_3126_, v_j_3128_);
lean_dec(v_j_3128_);
v___x_3141_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3130_, v_c_3129_, v_pos_3132_);
lean_dec(v_pos_3132_);
v_j_3128_ = v___x_3140_;
v_s_3130_ = v___x_3141_;
goto _start;
}
else
{
lean_object* v___x_3143_; 
lean_dec(v_j_3128_);
v___x_3143_ = l_Lean_Parser_ParserState_mkError(v_s_3130_, v_errorMsg_3127_);
return v___x_3143_;
}
}
}
else
{
lean_object* v___x_3144_; 
lean_dec(v_j_3128_);
v___x_3144_ = l_Lean_Parser_ParserState_mkError(v_s_3130_, v_errorMsg_3127_);
return v___x_3144_;
}
}
else
{
lean_dec(v_j_3128_);
lean_dec_ref(v_errorMsg_3127_);
return v_s_3130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3145_, lean_object* v_errorMsg_3146_, lean_object* v_j_3147_, lean_object* v_c_3148_, lean_object* v_s_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3145_, v_errorMsg_3146_, v_j_3147_, v_c_3148_, v_s_3149_);
lean_dec_ref(v_c_3148_);
lean_dec_ref(v_sym_3145_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3151_, lean_object* v_errorMsg_3152_, lean_object* v_j_3153_, lean_object* v_c_3154_, lean_object* v_s_3155_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3151_, v_errorMsg_3152_, v_j_3153_, v_c_3154_, v_s_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3157_, lean_object* v_errorMsg_3158_, lean_object* v_j_3159_, lean_object* v_c_3160_, lean_object* v_s_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_Parser_strAux(v_sym_3157_, v_errorMsg_3158_, v_j_3159_, v_c_3160_, v_s_3161_);
lean_dec_ref(v_c_3160_);
lean_dec_ref(v_sym_3157_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3163_, lean_object* v_i_3164_){
_start:
{
lean_object* v_zero_3165_; uint8_t v_isZero_3166_; 
v_zero_3165_ = lean_unsigned_to_nat(0u);
v_isZero_3166_ = lean_nat_dec_eq(v_i_3164_, v_zero_3165_);
if (v_isZero_3166_ == 1)
{
lean_object* v___x_3167_; 
lean_dec(v_i_3164_);
v___x_3167_ = lean_box(0);
return v___x_3167_;
}
else
{
lean_object* v_one_3168_; lean_object* v_n_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_one_3168_ = lean_unsigned_to_nat(1u);
v_n_3169_ = lean_nat_sub(v_i_3164_, v_one_3168_);
lean_dec(v_i_3164_);
v___x_3170_ = l_Subarray_get___redArg(v_as_3163_, v_n_3169_);
v___x_3171_ = l_Lean_Syntax_isNone(v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_dec(v_n_3169_);
v___x_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
return v___x_3172_;
}
else
{
lean_dec(v___x_3170_);
v_i_3164_ = v_n_3169_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3174_, lean_object* v_i_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3174_, v_i_3175_);
lean_dec_ref(v_as_3174_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3177_){
_start:
{
lean_object* v___x_3178_; lean_object* v_start_3179_; lean_object* v_stop_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3178_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3177_);
v_start_3179_ = lean_ctor_get(v___x_3178_, 1);
lean_inc(v_start_3179_);
v_stop_3180_ = lean_ctor_get(v___x_3178_, 2);
lean_inc(v_stop_3180_);
v___x_3181_ = lean_nat_sub(v_stop_3180_, v_start_3179_);
lean_dec(v_start_3179_);
lean_dec(v_stop_3180_);
v___x_3182_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3178_, v___x_3181_);
lean_dec_ref(v___x_3178_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_box(0);
return v___x_3183_;
}
else
{
lean_object* v_val_3184_; 
v_val_3184_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_val_3184_);
lean_dec_ref_known(v___x_3182_, 1);
return v_val_3184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3185_, lean_object* v_i_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3185_, v_i_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3189_, lean_object* v_i_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3189_, v_i_3190_, v_a_3191_);
lean_dec_ref(v_as_3189_);
return v_res_3192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Syntax_getTailInfo(v_prev_3193_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_trailing_3195_; lean_object* v_startPos_3196_; lean_object* v_stopPos_3197_; uint8_t v___x_3198_; 
v_trailing_3195_ = lean_ctor_get(v___x_3194_, 2);
lean_inc_ref(v_trailing_3195_);
lean_dec_ref_known(v___x_3194_, 4);
v_startPos_3196_ = lean_ctor_get(v_trailing_3195_, 1);
lean_inc(v_startPos_3196_);
v_stopPos_3197_ = lean_ctor_get(v_trailing_3195_, 2);
lean_inc(v_stopPos_3197_);
lean_dec_ref(v_trailing_3195_);
v___x_3198_ = lean_nat_dec_lt(v_startPos_3196_, v_stopPos_3197_);
lean_dec(v_stopPos_3197_);
lean_dec(v_startPos_3196_);
return v___x_3198_;
}
else
{
uint8_t v___x_3199_; 
lean_dec(v___x_3194_);
v___x_3199_ = 0;
return v___x_3199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3200_){
_start:
{
uint8_t v_res_3201_; lean_object* v_r_3202_; 
v_res_3201_ = l_Lean_Parser_checkTailWs(v_prev_3200_);
lean_dec(v_prev_3200_);
v_r_3202_ = lean_box(v_res_3201_);
return v_r_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3203_, lean_object* v_s_3204_){
_start:
{
lean_object* v_stxStack_3205_; lean_object* v_prev_3206_; uint8_t v___x_3207_; 
v_stxStack_3205_ = lean_ctor_get(v_s_3204_, 0);
lean_inc_ref(v_stxStack_3205_);
v_prev_3206_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3205_);
v___x_3207_ = l_Lean_Parser_checkTailWs(v_prev_3206_);
lean_dec(v_prev_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Parser_ParserState_mkError(v_s_3204_, v_errorMsg_3203_);
return v___x_3208_;
}
else
{
lean_dec_ref(v_errorMsg_3203_);
return v_s_3204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3209_, lean_object* v_x_3210_, lean_object* v_s_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3209_, v_s_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3213_, lean_object* v_x_3214_, lean_object* v_s_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3213_, v_x_3214_, v_s_3215_);
lean_dec_ref(v_x_3214_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3217_){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3219_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3219_, 0, v_errorMsg_3217_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3229_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3230_ = l_Lean_addBuiltinDocString(v___x_3228_, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3233_){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = l_String_instInhabitedSlice;
v___x_3235_ = lean_panic_fn_borrowed(v___x_3234_, v_msg_3233_);
return v___x_3235_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3236_, lean_object* v_a_3237_, uint8_t v_b_3238_){
_start:
{
lean_object* v_str_3239_; lean_object* v_startInclusive_3240_; lean_object* v_endExclusive_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v_str_3239_ = lean_ctor_get(v_s_3236_, 0);
v_startInclusive_3240_ = lean_ctor_get(v_s_3236_, 1);
v_endExclusive_3241_ = lean_ctor_get(v_s_3236_, 2);
v___x_3242_ = lean_nat_sub(v_endExclusive_3241_, v_startInclusive_3240_);
v___x_3243_ = lean_nat_dec_eq(v_a_3237_, v___x_3242_);
lean_dec(v___x_3242_);
if (v___x_3243_ == 0)
{
uint32_t v___x_3244_; lean_object* v___x_3245_; uint32_t v___x_3246_; uint8_t v___x_3247_; 
v___x_3244_ = 10;
v___x_3245_ = lean_nat_add(v_startInclusive_3240_, v_a_3237_);
lean_dec(v_a_3237_);
v___x_3246_ = lean_string_utf8_get_fast(v_str_3239_, v___x_3245_);
v___x_3247_ = lean_uint32_dec_eq(v___x_3246_, v___x_3244_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_string_utf8_next_fast(v_str_3239_, v___x_3245_);
lean_dec(v___x_3245_);
v___x_3249_ = lean_nat_sub(v___x_3248_, v_startInclusive_3240_);
v_a_3237_ = v___x_3249_;
v_b_3238_ = v___x_3247_;
goto _start;
}
else
{
lean_dec(v___x_3245_);
return v___x_3247_;
}
}
else
{
lean_dec(v_a_3237_);
return v_b_3238_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3251_, lean_object* v_a_3252_, lean_object* v_b_3253_){
_start:
{
uint8_t v_b_boxed_3254_; uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_b_boxed_3254_ = lean_unbox(v_b_3253_);
v_res_3255_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3251_, v_a_3252_, v_b_boxed_3254_);
lean_dec_ref(v_s_3251_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3257_){
_start:
{
lean_object* v_searcher_3258_; uint8_t v___x_3259_; uint8_t v___x_3260_; 
v_searcher_3258_ = lean_unsigned_to_nat(0u);
v___x_3259_ = 0;
v___x_3260_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3257_, v_searcher_3258_, v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3261_){
_start:
{
uint8_t v_res_3262_; lean_object* v_r_3263_; 
v_res_3262_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3261_);
lean_dec_ref(v_s_3261_);
v_r_3263_ = lean_box(v_res_3262_);
return v_r_3263_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3267_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3268_ = lean_unsigned_to_nat(14u);
v___x_3269_ = lean_unsigned_to_nat(22u);
v___x_3270_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3271_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3272_ = l_mkPanicMessageWithDecl(v___x_3271_, v___x_3270_, v___x_3269_, v___x_3268_, v___x_3267_);
return v___x_3272_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3273_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Syntax_getTailInfo(v_prev_3273_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_trailing_3279_; lean_object* v_str_3280_; lean_object* v_startPos_3281_; lean_object* v_stopPos_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3293_; 
v_trailing_3279_ = lean_ctor_get(v___x_3278_, 2);
lean_inc_ref(v_trailing_3279_);
lean_dec_ref_known(v___x_3278_, 4);
v_str_3280_ = lean_ctor_get(v_trailing_3279_, 0);
v_startPos_3281_ = lean_ctor_get(v_trailing_3279_, 1);
v_stopPos_3282_ = lean_ctor_get(v_trailing_3279_, 2);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_trailing_3279_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3284_ = v_trailing_3279_;
v_isShared_3285_ = v_isSharedCheck_3293_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_stopPos_3282_);
lean_inc(v_startPos_3281_);
lean_inc(v_str_3280_);
lean_dec(v_trailing_3279_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3293_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
uint8_t v___x_3286_; 
v___x_3286_ = lean_string_is_valid_pos(v_str_3280_, v_startPos_3281_);
if (v___x_3286_ == 0)
{
lean_del_object(v___x_3284_);
lean_dec(v_stopPos_3282_);
lean_dec(v_startPos_3281_);
lean_dec_ref(v_str_3280_);
goto v___jp_3274_;
}
else
{
uint8_t v___x_3287_; 
v___x_3287_ = lean_string_is_valid_pos(v_str_3280_, v_stopPos_3282_);
if (v___x_3287_ == 0)
{
lean_del_object(v___x_3284_);
lean_dec(v_stopPos_3282_);
lean_dec(v_startPos_3281_);
lean_dec_ref(v_str_3280_);
goto v___jp_3274_;
}
else
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_nat_dec_le(v_startPos_3281_, v_stopPos_3282_);
if (v___x_3288_ == 0)
{
lean_del_object(v___x_3284_);
lean_dec(v_stopPos_3282_);
lean_dec(v_startPos_3281_);
lean_dec_ref(v_str_3280_);
goto v___jp_3274_;
}
else
{
lean_object* v___x_3290_; 
if (v_isShared_3285_ == 0)
{
v___x_3290_ = v___x_3284_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_str_3280_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_startPos_3281_);
lean_ctor_set(v_reuseFailAlloc_3292_, 2, v_stopPos_3282_);
v___x_3290_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
uint8_t v___x_3291_; 
v___x_3291_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3290_);
lean_dec_ref(v___x_3290_);
return v___x_3291_;
}
}
}
}
}
}
else
{
uint8_t v___x_3294_; 
lean_dec(v___x_3278_);
v___x_3294_ = 0;
return v___x_3294_;
}
v___jp_3274_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3275_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3276_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3275_);
v___x_3277_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3276_);
lean_dec_ref(v___x_3276_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3295_){
_start:
{
uint8_t v_res_3296_; lean_object* v_r_3297_; 
v_res_3296_ = l_Lean_Parser_checkTailLinebreak(v_prev_3295_);
lean_dec(v_prev_3295_);
v_r_3297_ = lean_box(v_res_3296_);
return v_r_3297_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3298_, lean_object* v_inst_3299_, lean_object* v_R_3300_, lean_object* v_a_3301_, uint8_t v_b_3302_, lean_object* v_c_3303_){
_start:
{
uint8_t v___x_3304_; 
v___x_3304_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3298_, v_a_3301_, v_b_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3305_, lean_object* v_inst_3306_, lean_object* v_R_3307_, lean_object* v_a_3308_, lean_object* v_b_3309_, lean_object* v_c_3310_){
_start:
{
uint8_t v_b_boxed_3311_; uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_b_boxed_3311_ = lean_unbox(v_b_3309_);
v_res_3312_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3305_, v_inst_3306_, v_R_3307_, v_a_3308_, v_b_boxed_3311_, v_c_3310_);
lean_dec_ref(v_s_3305_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3314_, lean_object* v_s_3315_){
_start:
{
lean_object* v_stxStack_3316_; lean_object* v_prev_3317_; uint8_t v___x_3318_; 
v_stxStack_3316_ = lean_ctor_get(v_s_3315_, 0);
v_prev_3317_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3316_);
v___x_3318_ = l_Lean_Parser_checkTailLinebreak(v_prev_3317_);
lean_dec(v_prev_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Parser_ParserState_mkError(v_s_3315_, v_errorMsg_3314_);
return v___x_3319_;
}
else
{
lean_dec_ref(v_errorMsg_3314_);
return v_s_3315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3320_, lean_object* v_x_3321_, lean_object* v_s_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3320_, v_s_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3324_, lean_object* v_x_3325_, lean_object* v_s_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3324_, v_x_3325_, v_s_3326_);
lean_dec_ref(v_x_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3328_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3330_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3330_, 0, v_errorMsg_3328_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3340_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3341_ = l_Lean_addBuiltinDocString(v___x_3339_, v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3343_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3344_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Syntax_getTailInfo(v_prev_3344_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_trailing_3346_; lean_object* v_startPos_3347_; lean_object* v_stopPos_3348_; uint8_t v___x_3349_; 
v_trailing_3346_ = lean_ctor_get(v___x_3345_, 2);
lean_inc_ref(v_trailing_3346_);
lean_dec_ref_known(v___x_3345_, 4);
v_startPos_3347_ = lean_ctor_get(v_trailing_3346_, 1);
lean_inc(v_startPos_3347_);
v_stopPos_3348_ = lean_ctor_get(v_trailing_3346_, 2);
lean_inc(v_stopPos_3348_);
lean_dec_ref(v_trailing_3346_);
v___x_3349_ = lean_nat_dec_eq(v_stopPos_3348_, v_startPos_3347_);
lean_dec(v_startPos_3347_);
lean_dec(v_stopPos_3348_);
return v___x_3349_;
}
else
{
uint8_t v___x_3350_; 
lean_dec(v___x_3345_);
v___x_3350_ = 0;
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3351_){
_start:
{
uint8_t v_res_3352_; lean_object* v_r_3353_; 
v_res_3352_ = l_Lean_Parser_checkTailNoWs(v_prev_3351_);
lean_dec(v_prev_3351_);
v_r_3353_ = lean_box(v_res_3352_);
return v_r_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3354_, lean_object* v_s_3355_){
_start:
{
lean_object* v_stxStack_3356_; lean_object* v_prev_3357_; uint8_t v___x_3358_; 
v_stxStack_3356_ = lean_ctor_get(v_s_3355_, 0);
lean_inc_ref(v_stxStack_3356_);
v_prev_3357_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3356_);
v___x_3358_ = l_Lean_Parser_checkTailNoWs(v_prev_3357_);
lean_dec(v_prev_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Parser_ParserState_mkError(v_s_3355_, v_errorMsg_3354_);
return v___x_3359_;
}
else
{
lean_dec_ref(v_errorMsg_3354_);
return v_s_3355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3360_, lean_object* v_x_3361_, lean_object* v_s_3362_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3360_, v_s_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3364_, lean_object* v_x_3365_, lean_object* v_s_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3364_, v_x_3365_, v_s_3366_);
lean_dec_ref(v_x_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3370_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3370_, 0, v_errorMsg_3368_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3380_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3381_ = l_Lean_addBuiltinDocString(v___x_3379_, v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3384_, lean_object* v_asciiSym_3385_, lean_object* v_s_3386_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_string_dec_eq(v_s_3386_, v_sym_3384_);
if (v___x_3387_ == 0)
{
uint8_t v___x_3388_; 
v___x_3388_ = lean_string_dec_eq(v_s_3386_, v_asciiSym_3385_);
return v___x_3388_;
}
else
{
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3389_, lean_object* v_asciiSym_3390_, lean_object* v_s_3391_){
_start:
{
uint8_t v_res_3392_; lean_object* v_r_3393_; 
v_res_3392_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3389_, v_asciiSym_3390_, v_s_3391_);
lean_dec_ref(v_s_3391_);
lean_dec_ref(v_asciiSym_3390_);
lean_dec_ref(v_sym_3389_);
v_r_3393_ = lean_box(v_res_3392_);
return v_r_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3394_, lean_object* v_asciiSym_3395_, lean_object* v_expected_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___f_3399_; lean_object* v___x_3400_; 
v___f_3399_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3399_, 0, v_sym_3394_);
lean_closure_set(v___f_3399_, 1, v_asciiSym_3395_);
v___x_3400_ = l_Lean_Parser_satisfySymbolFn(v___f_3399_, v_expected_3396_, v_a_3397_, v_a_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3401_, lean_object* v_sym_3402_, lean_object* v_tks_3403_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_asciiSym_3401_);
lean_ctor_set(v___x_3404_, 1, v_tks_3403_);
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_sym_3402_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3406_, lean_object* v_asciiSym_3407_){
_start:
{
lean_object* v___f_3408_; lean_object* v___f_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_inc_ref(v_sym_3406_);
lean_inc_ref(v_asciiSym_3407_);
v___f_3408_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3408_, 0, v_asciiSym_3407_);
lean_closure_set(v___f_3408_, 1, v_sym_3406_);
v___f_3409_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3410_ = lean_box(0);
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_asciiSym_3407_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_sym_3406_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3414_, 0, v___f_3408_);
lean_ctor_set(v___x_3414_, 1, v___f_3409_);
lean_ctor_set(v___x_3414_, 2, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3416_, lean_object* v_asciiSym_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3420_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3421_ = lean_string_append(v___x_3420_, v_sym_3416_);
v___x_3422_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3423_ = lean_string_append(v___x_3421_, v___x_3422_);
v___x_3424_ = lean_string_append(v___x_3423_, v_asciiSym_3417_);
v___x_3425_ = lean_string_append(v___x_3424_, v___x_3420_);
v___x_3426_ = lean_box(0);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3416_, v_asciiSym_3417_, v___x_3427_, v_a_3418_, v_a_3419_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3429_, lean_object* v_asciiSym_3430_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v_str_3435_; lean_object* v_startInclusive_3436_; lean_object* v_endExclusive_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3454_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = lean_string_utf8_byte_size(v_sym_3429_);
v___x_3433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3433_, 0, v_sym_3429_);
lean_ctor_set(v___x_3433_, 1, v___x_3431_);
lean_ctor_set(v___x_3433_, 2, v___x_3432_);
v___x_3434_ = l_String_Slice_trimAscii(v___x_3433_);
v_str_3435_ = lean_ctor_get(v___x_3434_, 0);
v_startInclusive_3436_ = lean_ctor_get(v___x_3434_, 1);
v_endExclusive_3437_ = lean_ctor_get(v___x_3434_, 2);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3439_ = v___x_3434_;
v_isShared_3440_ = v_isSharedCheck_3454_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_endExclusive_3437_);
lean_inc(v_startInclusive_3436_);
lean_inc(v_str_3435_);
lean_dec(v___x_3434_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3454_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = lean_string_utf8_byte_size(v_asciiSym_3430_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 2, v___x_3441_);
lean_ctor_set(v___x_3439_, 1, v___x_3431_);
lean_ctor_set(v___x_3439_, 0, v_asciiSym_3430_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_asciiSym_3430_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v_str_3445_; lean_object* v_startInclusive_3446_; lean_object* v_endExclusive_3447_; lean_object* v_sym_3448_; lean_object* v_asciiSym_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3444_ = l_String_Slice_trimAscii(v___x_3443_);
v_str_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_ref(v_str_3445_);
v_startInclusive_3446_ = lean_ctor_get(v___x_3444_, 1);
lean_inc(v_startInclusive_3446_);
v_endExclusive_3447_ = lean_ctor_get(v___x_3444_, 2);
lean_inc(v_endExclusive_3447_);
lean_dec_ref(v___x_3444_);
v_sym_3448_ = lean_string_utf8_extract_fast(v_str_3435_, v_startInclusive_3436_, v_endExclusive_3437_);
lean_dec(v_endExclusive_3437_);
lean_dec(v_startInclusive_3436_);
lean_dec_ref(v_str_3435_);
v_asciiSym_3449_ = lean_string_utf8_extract_fast(v_str_3445_, v_startInclusive_3446_, v_endExclusive_3447_);
lean_dec(v_endExclusive_3447_);
lean_dec(v_startInclusive_3446_);
lean_dec_ref(v_str_3445_);
lean_inc_ref(v_asciiSym_3449_);
lean_inc_ref(v_sym_3448_);
v___x_3450_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3448_, v_asciiSym_3449_);
v___x_3451_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3451_, 0, v_sym_3448_);
lean_closure_set(v___x_3451_, 1, v_asciiSym_3449_);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
return v___x_3452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3455_, lean_object* v_asciiSym_3456_, uint8_t v_preserveForPP_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3455_, v_asciiSym_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3459_, lean_object* v_asciiSym_3460_, lean_object* v_preserveForPP_3461_){
_start:
{
uint8_t v_preserveForPP_boxed_3462_; lean_object* v_res_3463_; 
v_preserveForPP_boxed_3462_ = lean_unbox(v_preserveForPP_3461_);
v_res_3463_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3459_, v_asciiSym_3460_, v_preserveForPP_boxed_3462_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3464_){
_start:
{
lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___f_3465_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3466_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_k_3464_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3470_, 0, v___f_3465_);
lean_ctor_set(v___x_3470_, 1, v___f_3466_);
lean_ctor_set(v___x_3470_, 2, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3471_, lean_object* v_desc_3472_, lean_object* v_c_3473_, lean_object* v_s_3474_){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v_s_3477_; lean_object* v_stxStack_3478_; lean_object* v_errorMsg_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3475_ = lean_box(0);
lean_inc_ref(v_desc_3472_);
v___x_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_desc_3472_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v_s_3477_ = l_Lean_Parser_tokenFn(v___x_3476_, v_c_3473_, v_s_3474_);
v_stxStack_3478_ = lean_ctor_get(v_s_3477_, 0);
lean_inc_ref(v_stxStack_3478_);
v_errorMsg_3479_ = lean_ctor_get(v_s_3477_, 4);
lean_inc(v_errorMsg_3479_);
v___x_3480_ = lean_box(0);
v___x_3481_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3479_, v___x_3480_);
lean_dec(v_errorMsg_3479_);
if (v___x_3481_ == 0)
{
lean_dec_ref(v_stxStack_3478_);
lean_dec_ref(v_desc_3472_);
return v_s_3477_;
}
else
{
lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3482_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3478_);
lean_dec_ref(v_stxStack_3478_);
v___x_3483_ = l_Lean_Syntax_isOfKind(v___x_3482_, v_k_3471_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3477_, v_desc_3472_, v___x_3484_);
return v___x_3485_;
}
else
{
lean_dec_ref(v_desc_3472_);
return v_s_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3486_, lean_object* v_desc_3487_, lean_object* v_c_3488_, lean_object* v_s_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Parser_expectTokenFn(v_k_3486_, v_desc_3487_, v_c_3488_, v_s_3489_);
lean_dec(v_k_3486_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3494_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3495_ = l_Lean_Parser_expectTokenFn(v___x_3493_, v___x_3494_, v_a_3491_, v_a_3492_);
return v___x_3495_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3497_ = l_Lean_Parser_mkAtomicInfo(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3499_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3505_, lean_object* v_s_3506_){
_start:
{
lean_object* v_pos_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_pos_3507_ = lean_ctor_get(v_s_3506_, 2);
lean_inc(v_pos_3507_);
v___x_3508_ = 1;
v___x_3509_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3510_ = l_Lean_Parser_hexNumberFn(v_pos_3507_, v___x_3508_, v___x_3509_, v_ctx_3505_, v_s_3506_);
return v___x_3510_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3512_ = l_Lean_Parser_mkAtomicInfo(v___x_3511_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3514_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
lean_ctor_set(v___x_3515_, 1, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3521_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3522_ = l_Lean_Parser_expectTokenFn(v___x_3520_, v___x_3521_, v_a_3518_, v_a_3519_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3524_ = l_Lean_Parser_mkAtomicInfo(v___x_3523_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3526_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___x_3525_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3533_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3534_ = l_Lean_Parser_expectTokenFn(v___x_3532_, v___x_3533_, v_a_3530_, v_a_3531_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3536_ = l_Lean_Parser_mkAtomicInfo(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3538_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3545_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3546_ = l_Lean_Parser_expectTokenFn(v___x_3544_, v___x_3545_, v_a_3542_, v_a_3543_);
return v___x_3546_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3548_ = l_Lean_Parser_mkAtomicInfo(v___x_3547_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3550_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3560_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3561_ = l_Lean_Parser_expectTokenFn(v___x_3559_, v___x_3560_, v_a_3557_, v_a_3558_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3563_ = l_Lean_Parser_mkAtomicInfo(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3565_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
lean_ctor_set(v___x_3566_, 1, v___x_3564_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_c_3571_, lean_object* v_s_3572_){
_start:
{
lean_object* v_toCacheableParserContext_3573_; lean_object* v_forbiddenTks_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_toCacheableParserContext_3573_ = lean_ctor_get(v_c_3571_, 2);
v_forbiddenTks_3574_ = lean_ctor_get(v_toCacheableParserContext_3573_, 3);
v___x_3575_ = lean_array_get_size(v_forbiddenTks_3574_);
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = lean_nat_dec_eq(v___x_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v_pos_3578_; lean_object* v_iniSz_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_s_3582_; lean_object* v_stxStack_3583_; lean_object* v_errorMsg_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
lean_inc_ref(v_forbiddenTks_3574_);
v_pos_3578_ = lean_ctor_get(v_s_3572_, 2);
lean_inc(v_pos_3578_);
v_iniSz_3579_ = l_Lean_Parser_ParserState_stackSize(v_s_3572_);
v___x_3580_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3581_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v_s_3582_ = l_Lean_Parser_expectTokenFn(v___x_3580_, v___x_3581_, v_c_3571_, v_s_3572_);
v_stxStack_3583_ = lean_ctor_get(v_s_3582_, 0);
lean_inc_ref(v_stxStack_3583_);
v_errorMsg_3584_ = lean_ctor_get(v_s_3582_, 4);
lean_inc(v_errorMsg_3584_);
v___x_3585_ = lean_box(0);
v___x_3586_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3584_, v___x_3585_);
lean_dec(v_errorMsg_3584_);
if (v___x_3586_ == 0)
{
lean_dec_ref(v_stxStack_3583_);
lean_dec(v_iniSz_3579_);
lean_dec(v_pos_3578_);
lean_dec_ref(v_forbiddenTks_3574_);
return v_s_3582_;
}
else
{
if (v___x_3577_ == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3583_);
lean_dec_ref(v_stxStack_3583_);
if (lean_obj_tag(v___x_3587_) == 3)
{
lean_object* v_rawVal_3588_; lean_object* v_str_3589_; lean_object* v_startPos_3590_; lean_object* v_stopPos_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v_rawVal_3588_ = lean_ctor_get(v___x_3587_, 1);
lean_inc_ref(v_rawVal_3588_);
lean_dec_ref_known(v___x_3587_, 4);
v_str_3589_ = lean_ctor_get(v_rawVal_3588_, 0);
lean_inc_ref(v_str_3589_);
v_startPos_3590_ = lean_ctor_get(v_rawVal_3588_, 1);
lean_inc(v_startPos_3590_);
v_stopPos_3591_ = lean_ctor_get(v_rawVal_3588_, 2);
lean_inc(v_stopPos_3591_);
lean_dec_ref(v_rawVal_3588_);
v___x_3592_ = lean_string_utf8_extract(v_str_3589_, v_startPos_3590_, v_stopPos_3591_);
lean_dec(v_stopPos_3591_);
lean_dec(v_startPos_3590_);
lean_dec_ref(v_str_3589_);
v___x_3593_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_3574_, v___x_3592_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v_forbiddenTks_3574_);
if (v___x_3593_ == 0)
{
lean_dec(v_iniSz_3579_);
lean_dec(v_pos_3578_);
return v_s_3582_;
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_iniSz_3579_);
v___x_3596_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_3582_, v___x_3594_, v_pos_3578_, v___x_3595_);
lean_dec_ref_known(v___x_3595_, 1);
return v___x_3596_;
}
}
else
{
lean_dec(v___x_3587_);
lean_dec(v_iniSz_3579_);
lean_dec(v_pos_3578_);
lean_dec_ref(v_forbiddenTks_3574_);
return v_s_3582_;
}
}
else
{
lean_dec_ref(v_stxStack_3583_);
lean_dec(v_iniSz_3579_);
lean_dec(v_pos_3578_);
lean_dec_ref(v_forbiddenTks_3574_);
return v_s_3582_;
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3598_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3599_ = l_Lean_Parser_expectTokenFn(v___x_3597_, v___x_3598_, v_c_3571_, v_s_3572_);
return v___x_3599_;
}
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3601_ = l_Lean_Parser_mkAtomicInfo(v___x_3600_);
return v___x_3601_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3603_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v___x_3602_);
return v___x_3604_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3617_, lean_object* v_c_3618_, lean_object* v_s_3619_){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v_s_3622_; lean_object* v_stxStack_3623_; lean_object* v_errorMsg_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v___x_3620_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3621_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3622_ = l_Lean_Parser_tokenFn(v___x_3621_, v_c_3618_, v_s_3619_);
v_stxStack_3623_ = lean_ctor_get(v_s_3622_, 0);
lean_inc_ref(v_stxStack_3623_);
v_errorMsg_3624_ = lean_ctor_get(v_s_3622_, 4);
lean_inc(v_errorMsg_3624_);
v___x_3625_ = lean_box(0);
v___x_3626_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3624_, v___x_3625_);
lean_dec(v_errorMsg_3624_);
if (v___x_3626_ == 0)
{
lean_dec_ref(v_stxStack_3623_);
lean_dec(v_id_3617_);
return v_s_3622_;
}
else
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3623_);
lean_dec_ref(v_stxStack_3623_);
if (lean_obj_tag(v___x_3627_) == 3)
{
lean_object* v_val_3628_; uint8_t v___x_3629_; 
v_val_3628_ = lean_ctor_get(v___x_3627_, 2);
lean_inc(v_val_3628_);
lean_dec_ref_known(v___x_3627_, 4);
v___x_3629_ = lean_name_eq(v_val_3628_, v_id_3617_);
lean_dec(v_val_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3630_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3631_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3617_, v___x_3626_);
v___x_3632_ = lean_string_append(v___x_3630_, v___x_3631_);
lean_dec_ref(v___x_3631_);
v___x_3633_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3634_ = lean_string_append(v___x_3632_, v___x_3633_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3622_, v___x_3634_, v___x_3635_);
return v___x_3636_;
}
else
{
lean_dec(v_id_3617_);
return v_s_3622_;
}
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_dec(v___x_3627_);
lean_dec(v_id_3617_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3622_, v___x_3620_, v___x_3637_);
return v___x_3638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3639_){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3641_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3641_, 0, v_id_3639_);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3646_, lean_object* v_s_3647_){
_start:
{
lean_object* v_pos_3649_; lean_object* v_str_3650_; lean_object* v_trailing_3651_; lean_object* v_s_3652_; lean_object* v_stxStack_3664_; lean_object* v_pos_3665_; uint8_t v___x_3668_; 
v_stxStack_3664_ = lean_ctor_get(v_s_3647_, 0);
v_pos_3665_ = lean_ctor_get(v_s_3647_, 2);
v___x_3668_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3664_);
if (v___x_3668_ == 0)
{
lean_object* v_prev_3669_; lean_object* v___x_3670_; 
v_prev_3669_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3664_);
v___x_3670_ = l_Lean_Syntax_getTailInfo(v_prev_3669_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_leading_3671_; lean_object* v_pos_3672_; lean_object* v_trailing_3673_; lean_object* v_endPos_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3685_; 
v_leading_3671_ = lean_ctor_get(v___x_3670_, 0);
v_pos_3672_ = lean_ctor_get(v___x_3670_, 1);
v_trailing_3673_ = lean_ctor_get(v___x_3670_, 2);
v_endPos_3674_ = lean_ctor_get(v___x_3670_, 3);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3676_ = v___x_3670_;
v_isShared_3677_ = v_isSharedCheck_3685_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_endPos_3674_);
lean_inc(v_trailing_3673_);
lean_inc(v_pos_3672_);
lean_inc(v_leading_3671_);
lean_dec(v___x_3670_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3685_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_str_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
lean_inc_n(v_endPos_3674_, 2);
v_str_3678_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3646_, v_endPos_3674_);
v___x_3679_ = l_Lean_Parser_ParserState_popSyntax(v_s_3647_);
lean_inc_ref(v_str_3678_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 2, v_str_3678_);
v___x_3681_ = v___x_3676_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_leading_3671_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_pos_3672_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_str_3678_);
lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_endPos_3674_);
v___x_3681_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; lean_object* v_s_3683_; 
v___x_3682_ = l_Lean_Syntax_setTailInfo(v_prev_3669_, v___x_3681_);
v_s_3683_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3679_, v___x_3682_);
v_pos_3649_ = v_endPos_3674_;
v_str_3650_ = v_str_3678_;
v_trailing_3651_ = v_trailing_3673_;
v_s_3652_ = v_s_3683_;
goto v___jp_3648_;
}
}
}
else
{
lean_inc(v_pos_3665_);
lean_dec(v___x_3670_);
lean_dec(v_prev_3669_);
goto v___jp_3666_;
}
}
else
{
lean_inc(v_pos_3665_);
goto v___jp_3666_;
}
v___jp_3648_:
{
lean_object* v_info_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_ident_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_inc(v_pos_3649_);
lean_inc_ref(v_str_3650_);
v_info_3653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3653_, 0, v_str_3650_);
lean_ctor_set(v_info_3653_, 1, v_pos_3649_);
lean_ctor_set(v_info_3653_, 2, v_trailing_3651_);
lean_ctor_set(v_info_3653_, 3, v_pos_3649_);
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_box(0);
v_ident_3656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3656_, 0, v_info_3653_);
lean_ctor_set(v_ident_3656_, 1, v_str_3650_);
lean_ctor_set(v_ident_3656_, 2, v___x_3654_);
lean_ctor_set(v_ident_3656_, 3, v___x_3655_);
v___x_3657_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_mk_empty_array_with_capacity(v___x_3658_);
v___x_3660_ = lean_array_push(v___x_3659_, v_ident_3656_);
v___x_3661_ = lean_box(2);
v___x_3662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
lean_ctor_set(v___x_3662_, 1, v___x_3657_);
lean_ctor_set(v___x_3662_, 2, v___x_3660_);
v___x_3663_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3652_, v___x_3662_);
return v___x_3663_;
}
v___jp_3666_:
{
lean_object* v_str_3667_; 
lean_inc(v_pos_3665_);
v_str_3667_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3646_, v_pos_3665_);
lean_inc_ref(v_str_3667_);
v_pos_3649_ = v_pos_3665_;
v_str_3650_ = v_str_3667_;
v_trailing_3651_ = v_str_3667_;
v_s_3652_ = v_s_3647_;
goto v___jp_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3686_, lean_object* v_s_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_Parser_hygieneInfoFn(v_c_3686_, v_s_3687_);
lean_dec_ref(v_c_3686_);
return v_res_3688_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3690_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3691_ = l_Lean_Parser_nodeInfo(v___x_3690_, v___x_3689_);
return v___x_3691_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3693_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v___x_3692_);
return v___x_3694_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3696_, lean_object* v_startStackSize_3697_){
_start:
{
lean_object* v_node_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_node_3698_ = l_Lean_Parser_SyntaxStack_back(v_s_3696_);
v___x_3699_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3696_, v_startStackSize_3697_);
v___x_3700_ = l_Lean_Parser_SyntaxStack_push(v___x_3699_, v_node_3698_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3701_, lean_object* v_startStackSize_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Parser_ParserState_keepTop(v_s_3701_, v_startStackSize_3702_);
lean_dec(v_startStackSize_3702_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3704_, lean_object* v_oldStackSize_3705_){
_start:
{
lean_object* v_stxStack_3706_; lean_object* v_lhsPrec_3707_; lean_object* v_pos_3708_; lean_object* v_cache_3709_; lean_object* v_errorMsg_3710_; lean_object* v_recoveredErrors_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3719_; 
v_stxStack_3706_ = lean_ctor_get(v_s_3704_, 0);
v_lhsPrec_3707_ = lean_ctor_get(v_s_3704_, 1);
v_pos_3708_ = lean_ctor_get(v_s_3704_, 2);
v_cache_3709_ = lean_ctor_get(v_s_3704_, 3);
v_errorMsg_3710_ = lean_ctor_get(v_s_3704_, 4);
v_recoveredErrors_3711_ = lean_ctor_get(v_s_3704_, 5);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_s_3704_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3713_ = v_s_3704_;
v_isShared_3714_ = v_isSharedCheck_3719_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_recoveredErrors_3711_);
lean_inc(v_errorMsg_3710_);
lean_inc(v_cache_3709_);
lean_inc(v_pos_3708_);
lean_inc(v_lhsPrec_3707_);
lean_inc(v_stxStack_3706_);
lean_dec(v_s_3704_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3719_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3706_, v_oldStackSize_3705_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3715_);
v___x_3717_ = v___x_3713_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_lhsPrec_3707_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_pos_3708_);
lean_ctor_set(v_reuseFailAlloc_3718_, 3, v_cache_3709_);
lean_ctor_set(v_reuseFailAlloc_3718_, 4, v_errorMsg_3710_);
lean_ctor_set(v_reuseFailAlloc_3718_, 5, v_recoveredErrors_3711_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3720_, lean_object* v_oldStackSize_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Parser_ParserState_keepNewError(v_s_3720_, v_oldStackSize_3721_);
lean_dec(v_oldStackSize_3721_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3723_, lean_object* v_oldStackSize_3724_, lean_object* v_oldStopPos_3725_, lean_object* v_oldError_3726_, lean_object* v_oldLhsPrec_3727_){
_start:
{
lean_object* v_stxStack_3728_; lean_object* v_cache_3729_; lean_object* v_recoveredErrors_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3738_; 
v_stxStack_3728_ = lean_ctor_get(v_s_3723_, 0);
v_cache_3729_ = lean_ctor_get(v_s_3723_, 3);
v_recoveredErrors_3730_ = lean_ctor_get(v_s_3723_, 5);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_s_3723_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; 
v_unused_3739_ = lean_ctor_get(v_s_3723_, 4);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_s_3723_, 2);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_s_3723_, 1);
lean_dec(v_unused_3741_);
v___x_3732_ = v_s_3723_;
v_isShared_3733_ = v_isSharedCheck_3738_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_recoveredErrors_3730_);
lean_inc(v_cache_3729_);
lean_inc(v_stxStack_3728_);
lean_dec(v_s_3723_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3738_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3728_, v_oldStackSize_3724_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 4, v_oldError_3726_);
lean_ctor_set(v___x_3732_, 2, v_oldStopPos_3725_);
lean_ctor_set(v___x_3732_, 1, v_oldLhsPrec_3727_);
lean_ctor_set(v___x_3732_, 0, v___x_3734_);
v___x_3736_ = v___x_3732_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_oldLhsPrec_3727_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_oldStopPos_3725_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_cache_3729_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_oldError_3726_);
lean_ctor_set(v_reuseFailAlloc_3737_, 5, v_recoveredErrors_3730_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3742_, lean_object* v_oldStackSize_3743_, lean_object* v_oldStopPos_3744_, lean_object* v_oldError_3745_, lean_object* v_oldLhsPrec_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3742_, v_oldStackSize_3743_, v_oldStopPos_3744_, v_oldError_3745_, v_oldLhsPrec_3746_);
lean_dec(v_oldStackSize_3743_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3748_, lean_object* v_oldStackSize_3749_, lean_object* v_oldError_3750_){
_start:
{
lean_object* v_stxStack_3751_; lean_object* v_lhsPrec_3752_; lean_object* v_pos_3753_; lean_object* v_cache_3754_; lean_object* v_errorMsg_3755_; lean_object* v_recoveredErrors_3756_; lean_object* v___y_3758_; 
v_stxStack_3751_ = lean_ctor_get(v_s_3748_, 0);
v_lhsPrec_3752_ = lean_ctor_get(v_s_3748_, 1);
v_pos_3753_ = lean_ctor_get(v_s_3748_, 2);
v_cache_3754_ = lean_ctor_get(v_s_3748_, 3);
v_errorMsg_3755_ = lean_ctor_get(v_s_3748_, 4);
v_recoveredErrors_3756_ = lean_ctor_get(v_s_3748_, 5);
if (lean_obj_tag(v_errorMsg_3755_) == 1)
{
lean_object* v_val_3762_; uint8_t v___x_3763_; 
lean_inc_ref(v_errorMsg_3755_);
lean_inc_ref(v_recoveredErrors_3756_);
lean_inc_ref(v_cache_3754_);
lean_inc(v_pos_3753_);
lean_inc(v_lhsPrec_3752_);
lean_inc_ref(v_stxStack_3751_);
lean_dec_ref(v_s_3748_);
v_val_3762_ = lean_ctor_get(v_errorMsg_3755_, 0);
lean_inc(v_val_3762_);
lean_dec_ref_known(v_errorMsg_3755_, 1);
v___x_3763_ = l_Lean_Parser_instBEqError_beq(v_oldError_3750_, v_val_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Parser_Error_merge(v_oldError_3750_, v_val_3762_);
v___y_3758_ = v___x_3764_;
goto v___jp_3757_;
}
else
{
lean_dec_ref(v_oldError_3750_);
v___y_3758_ = v_val_3762_;
goto v___jp_3757_;
}
}
else
{
lean_dec_ref(v_oldError_3750_);
return v_s_3748_;
}
v___jp_3757_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3751_, v_oldStackSize_3749_);
v___x_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___y_3758_);
v___x_3761_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v_lhsPrec_3752_);
lean_ctor_set(v___x_3761_, 2, v_pos_3753_);
lean_ctor_set(v___x_3761_, 3, v_cache_3754_);
lean_ctor_set(v___x_3761_, 4, v___x_3760_);
lean_ctor_set(v___x_3761_, 5, v_recoveredErrors_3756_);
return v___x_3761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3765_, lean_object* v_oldStackSize_3766_, lean_object* v_oldError_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3765_, v_oldStackSize_3766_, v_oldError_3767_);
lean_dec(v_oldStackSize_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3769_, lean_object* v_startStackSize_3770_){
_start:
{
lean_object* v_stxStack_3771_; lean_object* v_lhsPrec_3772_; lean_object* v_pos_3773_; lean_object* v_cache_3774_; lean_object* v_recoveredErrors_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3784_; 
v_stxStack_3771_ = lean_ctor_get(v_s_3769_, 0);
v_lhsPrec_3772_ = lean_ctor_get(v_s_3769_, 1);
v_pos_3773_ = lean_ctor_get(v_s_3769_, 2);
v_cache_3774_ = lean_ctor_get(v_s_3769_, 3);
v_recoveredErrors_3775_ = lean_ctor_get(v_s_3769_, 5);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_s_3769_);
if (v_isSharedCheck_3784_ == 0)
{
lean_object* v_unused_3785_; 
v_unused_3785_ = lean_ctor_get(v_s_3769_, 4);
lean_dec(v_unused_3785_);
v___x_3777_ = v_s_3769_;
v_isShared_3778_ = v_isSharedCheck_3784_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_recoveredErrors_3775_);
lean_inc(v_cache_3774_);
lean_inc(v_pos_3773_);
lean_inc(v_lhsPrec_3772_);
lean_inc(v_stxStack_3771_);
lean_dec(v_s_3769_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3784_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3779_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3771_, v_startStackSize_3770_);
v___x_3780_ = lean_box(0);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 4, v___x_3780_);
lean_ctor_set(v___x_3777_, 0, v___x_3779_);
v___x_3782_ = v___x_3777_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_lhsPrec_3772_);
lean_ctor_set(v_reuseFailAlloc_3783_, 2, v_pos_3773_);
lean_ctor_set(v_reuseFailAlloc_3783_, 3, v_cache_3774_);
lean_ctor_set(v_reuseFailAlloc_3783_, 4, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3783_, 5, v_recoveredErrors_3775_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3786_, lean_object* v_startStackSize_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Parser_ParserState_keepLatest(v_s_3786_, v_startStackSize_3787_);
lean_dec(v_startStackSize_3787_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3789_, lean_object* v_startStackSize_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Parser_ParserState_keepLatest(v_s_3789_, v_startStackSize_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3792_, lean_object* v_startStackSize_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3792_, v_startStackSize_3793_);
lean_dec(v_startStackSize_3793_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3796_){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3798_ = l_Lean_Parser_ParserState_mkError(v_s_3796_, v___x_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3799_, lean_object* v_startLhsPrec_3800_, lean_object* v_p_3801_, lean_object* v_c_3802_, lean_object* v_s_3803_){
_start:
{
lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3811_; lean_object* v_s_3812_; lean_object* v_stxStack_3822_; lean_object* v_pos_3823_; lean_object* v_cache_3824_; lean_object* v_errorMsg_3825_; lean_object* v_recoveredErrors_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3839_; 
v_stxStack_3822_ = lean_ctor_get(v_s_3803_, 0);
v_pos_3823_ = lean_ctor_get(v_s_3803_, 2);
v_cache_3824_ = lean_ctor_get(v_s_3803_, 3);
v_errorMsg_3825_ = lean_ctor_get(v_s_3803_, 4);
v_recoveredErrors_3826_ = lean_ctor_get(v_s_3803_, 5);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_s_3803_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v_s_3803_, 1);
lean_dec(v_unused_3840_);
v___x_3828_ = v_s_3803_;
v_isShared_3829_ = v_isSharedCheck_3839_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_recoveredErrors_3826_);
lean_inc(v_errorMsg_3825_);
lean_inc(v_cache_3824_);
lean_inc(v_pos_3823_);
lean_inc(v_stxStack_3822_);
lean_dec(v_s_3803_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3839_;
goto v_resetjp_3827_;
}
v___jp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = l_Lean_Parser_ParserState_shrinkStack(v___y_3806_, v___y_3805_);
lean_dec(v___y_3805_);
v___x_3808_ = lean_box(0);
v___x_3809_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3807_, v___x_3808_);
return v___x_3809_;
}
v___jp_3810_:
{
lean_object* v_s_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_s_3813_ = lean_apply_2(v_p_3801_, v_c_3802_, v_s_3812_);
v___x_3814_ = l_Lean_Parser_ParserState_stackSize(v_s_3813_);
v___x_3815_ = lean_unsigned_to_nat(1u);
v___x_3816_ = lean_nat_add(v___y_3811_, v___x_3815_);
v___x_3817_ = lean_nat_dec_eq(v___x_3814_, v___x_3816_);
lean_dec(v___x_3816_);
lean_dec(v___x_3814_);
if (v___x_3817_ == 0)
{
lean_object* v_errorMsg_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
v_errorMsg_3818_ = lean_ctor_get(v_s_3813_, 4);
lean_inc(v_errorMsg_3818_);
v___x_3819_ = lean_box(0);
v___x_3820_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3818_, v___x_3819_);
lean_dec(v_errorMsg_3818_);
if (v___x_3820_ == 0)
{
v___y_3805_ = v___y_3811_;
v___y_3806_ = v_s_3813_;
goto v___jp_3804_;
}
else
{
if (v___x_3817_ == 0)
{
lean_object* v___x_3821_; 
lean_dec(v___y_3811_);
v___x_3821_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3813_);
return v___x_3821_;
}
else
{
v___y_3805_ = v___y_3811_;
v___y_3806_ = v_s_3813_;
goto v___jp_3804_;
}
}
}
else
{
lean_dec(v___y_3811_);
return v_s_3813_;
}
}
v_resetjp_3827_:
{
lean_object* v___y_3831_; 
if (lean_obj_tag(v_left_x3f_3799_) == 0)
{
lean_object* v___x_3838_; 
lean_dec(v_startLhsPrec_3800_);
v___x_3838_ = l_Lean_Parser_maxPrec;
v___y_3831_ = v___x_3838_;
goto v___jp_3830_;
}
else
{
v___y_3831_ = v_startLhsPrec_3800_;
goto v___jp_3830_;
}
v___jp_3830_:
{
lean_object* v_s_3833_; 
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 1, v___y_3831_);
v_s_3833_ = v___x_3828_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_stxStack_3822_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___y_3831_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v_pos_3823_);
lean_ctor_set(v_reuseFailAlloc_3837_, 3, v_cache_3824_);
lean_ctor_set(v_reuseFailAlloc_3837_, 4, v_errorMsg_3825_);
lean_ctor_set(v_reuseFailAlloc_3837_, 5, v_recoveredErrors_3826_);
v_s_3833_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v_startSize_3834_; 
v_startSize_3834_ = l_Lean_Parser_ParserState_stackSize(v_s_3833_);
if (lean_obj_tag(v_left_x3f_3799_) == 1)
{
lean_object* v_val_3835_; lean_object* v_s_3836_; 
v_val_3835_ = lean_ctor_get(v_left_x3f_3799_, 0);
lean_inc(v_val_3835_);
lean_dec_ref_known(v_left_x3f_3799_, 1);
v_s_3836_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3833_, v_val_3835_);
v___y_3811_ = v_startSize_3834_;
v_s_3812_ = v_s_3836_;
goto v___jp_3810_;
}
else
{
lean_dec(v_left_x3f_3799_);
v___y_3811_ = v_startSize_3834_;
v_s_3812_ = v_s_3833_;
goto v___jp_3810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3841_, lean_object* v_prio_3842_){
_start:
{
lean_object* v_pos_3843_; lean_object* v_errorMsg_3844_; lean_object* v___y_3846_; 
v_pos_3843_ = lean_ctor_get(v_s_3841_, 2);
v_errorMsg_3844_ = lean_ctor_get(v_s_3841_, 4);
if (lean_obj_tag(v_errorMsg_3844_) == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_unsigned_to_nat(1u);
v___y_3846_ = v___x_3849_;
goto v___jp_3845_;
}
else
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_unsigned_to_nat(0u);
v___y_3846_ = v___x_3850_;
goto v___jp_3845_;
}
v___jp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___y_3846_);
lean_ctor_set(v___x_3847_, 1, v_prio_3842_);
lean_inc(v_pos_3843_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_pos_3843_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
return v___x_3848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3851_, lean_object* v_prio_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3851_, v_prio_3852_);
lean_dec_ref(v_s_3851_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3854_, lean_object* v_startSize_3855_, lean_object* v_startLhsPrec_3856_, lean_object* v_startPos_3857_, lean_object* v_prevPrio_3858_, lean_object* v_prio_3859_, lean_object* v_p_3860_, lean_object* v_c_3861_, lean_object* v_s_3862_){
_start:
{
lean_object* v_lhsPrec_3863_; lean_object* v_pos_3864_; lean_object* v_errorMsg_3865_; lean_object* v_previousScore_3866_; lean_object* v_fst_3867_; lean_object* v_snd_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3924_; 
v_lhsPrec_3863_ = lean_ctor_get(v_s_3862_, 1);
lean_inc(v_lhsPrec_3863_);
v_pos_3864_ = lean_ctor_get(v_s_3862_, 2);
lean_inc(v_pos_3864_);
v_errorMsg_3865_ = lean_ctor_get(v_s_3862_, 4);
lean_inc(v_errorMsg_3865_);
lean_inc(v_prevPrio_3858_);
v_previousScore_3866_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3862_, v_prevPrio_3858_);
v_fst_3867_ = lean_ctor_get(v_previousScore_3866_, 0);
v_snd_3868_ = lean_ctor_get(v_previousScore_3866_, 1);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_previousScore_3866_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3870_ = v_previousScore_3866_;
v_isShared_3871_ = v_isSharedCheck_3924_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_snd_3868_);
lean_inc(v_fst_3867_);
lean_dec(v_previousScore_3866_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3924_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_prevSize_3872_; lean_object* v_s_3873_; lean_object* v_s_3874_; lean_object* v___x_3883_; lean_object* v_fst_3884_; lean_object* v_snd_3885_; uint8_t v___x_3886_; 
v_prevSize_3872_ = l_Lean_Parser_ParserState_stackSize(v_s_3862_);
v_s_3873_ = l_Lean_Parser_ParserState_restore(v_s_3862_, v_prevSize_3872_, v_startPos_3857_);
v_s_3874_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3854_, v_startLhsPrec_3856_, v_p_3860_, v_c_3861_, v_s_3873_);
lean_inc(v_prio_3859_);
v___x_3883_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3874_, v_prio_3859_);
v_fst_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_fst_3884_);
v_snd_3885_ = lean_ctor_get(v___x_3883_, 1);
lean_inc(v_snd_3885_);
lean_dec_ref(v___x_3883_);
v___x_3886_ = lean_nat_dec_lt(v_fst_3867_, v_fst_3884_);
if (v___x_3886_ == 0)
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_nat_dec_eq(v_fst_3867_, v_fst_3884_);
lean_dec(v_fst_3884_);
lean_dec(v_fst_3867_);
if (v___x_3887_ == 0)
{
lean_dec(v_snd_3885_);
lean_del_object(v___x_3870_);
lean_dec(v_snd_3868_);
lean_dec(v_prio_3859_);
goto v___jp_3880_;
}
else
{
lean_object* v_fst_3888_; lean_object* v_snd_3889_; lean_object* v_fst_3890_; lean_object* v_snd_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3923_; 
v_fst_3888_ = lean_ctor_get(v_snd_3868_, 0);
lean_inc(v_fst_3888_);
v_snd_3889_ = lean_ctor_get(v_snd_3868_, 1);
lean_inc(v_snd_3889_);
lean_dec(v_snd_3868_);
v_fst_3890_ = lean_ctor_get(v_snd_3885_, 0);
v_snd_3891_ = lean_ctor_get(v_snd_3885_, 1);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_snd_3885_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3893_ = v_snd_3885_;
v_isShared_3894_ = v_isSharedCheck_3923_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_snd_3891_);
lean_inc(v_fst_3890_);
lean_dec(v_snd_3885_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3923_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
uint8_t v___x_3895_; 
v___x_3895_ = lean_nat_dec_lt(v_fst_3888_, v_fst_3890_);
if (v___x_3895_ == 0)
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_nat_dec_eq(v_fst_3888_, v_fst_3890_);
lean_dec(v_fst_3890_);
lean_dec(v_fst_3888_);
if (v___x_3896_ == 0)
{
lean_del_object(v___x_3893_);
lean_dec(v_snd_3891_);
lean_dec(v_snd_3889_);
lean_del_object(v___x_3870_);
lean_dec(v_prio_3859_);
goto v___jp_3880_;
}
else
{
uint8_t v___x_3897_; 
v___x_3897_ = lean_nat_dec_lt(v_snd_3889_, v_snd_3891_);
if (v___x_3897_ == 0)
{
uint8_t v___x_3898_; 
lean_del_object(v___x_3870_);
v___x_3898_ = lean_nat_dec_eq(v_snd_3889_, v_snd_3891_);
lean_dec(v_snd_3891_);
lean_dec(v_snd_3889_);
if (v___x_3898_ == 0)
{
lean_del_object(v___x_3893_);
lean_dec(v_prio_3859_);
goto v___jp_3880_;
}
else
{
lean_dec(v_pos_3864_);
lean_dec(v_prevPrio_3858_);
if (lean_obj_tag(v_errorMsg_3865_) == 0)
{
lean_object* v_stxStack_3899_; lean_object* v_lhsPrec_3900_; lean_object* v_pos_3901_; lean_object* v_cache_3902_; lean_object* v_errorMsg_3903_; lean_object* v_recoveredErrors_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v_prevSize_3872_);
v_stxStack_3899_ = lean_ctor_get(v_s_3874_, 0);
v_lhsPrec_3900_ = lean_ctor_get(v_s_3874_, 1);
v_pos_3901_ = lean_ctor_get(v_s_3874_, 2);
v_cache_3902_ = lean_ctor_get(v_s_3874_, 3);
v_errorMsg_3903_ = lean_ctor_get(v_s_3874_, 4);
v_recoveredErrors_3904_ = lean_ctor_get(v_s_3874_, 5);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_s_3874_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3906_ = v_s_3874_;
v_isShared_3907_ = v_isSharedCheck_3917_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_recoveredErrors_3904_);
lean_inc(v_errorMsg_3903_);
lean_inc(v_cache_3902_);
lean_inc(v_pos_3901_);
lean_inc(v_lhsPrec_3900_);
lean_inc(v_stxStack_3899_);
lean_dec(v_s_3874_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3917_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___y_3909_; uint8_t v___x_3916_; 
v___x_3916_ = lean_nat_dec_le(v_lhsPrec_3900_, v_lhsPrec_3863_);
if (v___x_3916_ == 0)
{
lean_dec(v_lhsPrec_3900_);
v___y_3909_ = v_lhsPrec_3863_;
goto v___jp_3908_;
}
else
{
lean_dec(v_lhsPrec_3863_);
v___y_3909_ = v_lhsPrec_3900_;
goto v___jp_3908_;
}
v___jp_3908_:
{
lean_object* v___x_3911_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 1, v___y_3909_);
v___x_3911_ = v___x_3906_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_stxStack_3899_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___y_3909_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_pos_3901_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v_cache_3902_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v_errorMsg_3903_);
lean_ctor_set(v_reuseFailAlloc_3915_, 5, v_recoveredErrors_3904_);
v___x_3911_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3913_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 1, v_prio_3859_);
lean_ctor_set(v___x_3893_, 0, v___x_3911_);
v___x_3913_ = v___x_3893_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_prio_3859_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
else
{
lean_object* v_val_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_dec(v_lhsPrec_3863_);
v_val_3918_ = lean_ctor_get(v_errorMsg_3865_, 0);
lean_inc(v_val_3918_);
lean_dec_ref_known(v_errorMsg_3865_, 1);
v___x_3919_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3874_, v_prevSize_3872_, v_val_3918_);
lean_dec(v_prevSize_3872_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 1, v_prio_3859_);
lean_ctor_set(v___x_3893_, 0, v___x_3919_);
v___x_3921_ = v___x_3893_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_prio_3859_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_del_object(v___x_3893_);
lean_dec(v_snd_3891_);
lean_dec(v_snd_3889_);
lean_dec(v_prevSize_3872_);
lean_dec(v_errorMsg_3865_);
lean_dec(v_pos_3864_);
lean_dec(v_lhsPrec_3863_);
lean_dec(v_prevPrio_3858_);
goto v___jp_3875_;
}
}
}
else
{
lean_del_object(v___x_3893_);
lean_dec(v_snd_3891_);
lean_dec(v_fst_3890_);
lean_dec(v_snd_3889_);
lean_dec(v_fst_3888_);
lean_dec(v_prevSize_3872_);
lean_dec(v_errorMsg_3865_);
lean_dec(v_pos_3864_);
lean_dec(v_lhsPrec_3863_);
lean_dec(v_prevPrio_3858_);
goto v___jp_3875_;
}
}
}
}
else
{
lean_dec(v_snd_3885_);
lean_dec(v_fst_3884_);
lean_dec(v_prevSize_3872_);
lean_dec(v_snd_3868_);
lean_dec(v_fst_3867_);
lean_dec(v_errorMsg_3865_);
lean_dec(v_pos_3864_);
lean_dec(v_lhsPrec_3863_);
lean_dec(v_prevPrio_3858_);
goto v___jp_3875_;
}
v___jp_3875_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = l_Lean_Parser_ParserState_keepNewError(v_s_3874_, v_startSize_3855_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v_prio_3859_);
lean_ctor_set(v___x_3870_, 0, v___x_3876_);
v___x_3878_ = v___x_3870_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_prio_3859_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
v___jp_3880_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3874_, v_prevSize_3872_, v_pos_3864_, v_errorMsg_3865_, v_lhsPrec_3863_);
lean_dec(v_prevSize_3872_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v_prevPrio_3858_);
return v___x_3882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3925_, lean_object* v_startSize_3926_, lean_object* v_startLhsPrec_3927_, lean_object* v_startPos_3928_, lean_object* v_prevPrio_3929_, lean_object* v_prio_3930_, lean_object* v_p_3931_, lean_object* v_c_3932_, lean_object* v_s_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3925_, v_startSize_3926_, v_startLhsPrec_3927_, v_startPos_3928_, v_prevPrio_3929_, v_prio_3930_, v_p_3931_, v_c_3932_, v_s_3933_);
lean_dec(v_startSize_3926_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3935_, lean_object* v_s_3936_){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; 
v___x_3937_ = lean_unsigned_to_nat(1u);
v___x_3938_ = lean_nat_add(v_startSize_3935_, v___x_3937_);
v___x_3939_ = l_Lean_Parser_ParserState_stackSize(v_s_3936_);
v___x_3940_ = lean_nat_dec_lt(v___x_3938_, v___x_3939_);
lean_dec(v___x_3939_);
lean_dec(v___x_3938_);
if (v___x_3940_ == 0)
{
return v_s_3936_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3942_ = l_Lean_Parser_ParserState_mkNode(v_s_3936_, v___x_3941_, v_startSize_3935_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3943_, lean_object* v_s_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3943_, v_s_3944_);
lean_dec(v_startSize_3943_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3946_, lean_object* v_startSize_3947_, lean_object* v_startLhsPrec_3948_, lean_object* v_startPos_3949_, lean_object* v_prevPrio_3950_, lean_object* v_ps_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
if (lean_obj_tag(v_ps_3951_) == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v_a_3952_);
lean_dec(v_prevPrio_3950_);
lean_dec(v_startPos_3949_);
lean_dec(v_startLhsPrec_3948_);
lean_dec(v_left_x3f_3946_);
v___x_3954_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3947_, v_a_3953_);
return v___x_3954_;
}
else
{
lean_object* v_head_3955_; lean_object* v_fst_3956_; lean_object* v_tail_3957_; lean_object* v_snd_3958_; lean_object* v_fn_3959_; lean_object* v___x_3960_; lean_object* v_fst_3961_; lean_object* v_snd_3962_; 
v_head_3955_ = lean_ctor_get(v_ps_3951_, 0);
lean_inc(v_head_3955_);
v_fst_3956_ = lean_ctor_get(v_head_3955_, 0);
lean_inc(v_fst_3956_);
v_tail_3957_ = lean_ctor_get(v_ps_3951_, 1);
lean_inc(v_tail_3957_);
lean_dec_ref_known(v_ps_3951_, 2);
v_snd_3958_ = lean_ctor_get(v_head_3955_, 1);
lean_inc(v_snd_3958_);
lean_dec(v_head_3955_);
v_fn_3959_ = lean_ctor_get(v_fst_3956_, 1);
lean_inc_ref(v_fn_3959_);
lean_dec(v_fst_3956_);
lean_inc_ref(v_a_3952_);
lean_inc(v_startPos_3949_);
lean_inc(v_startLhsPrec_3948_);
lean_inc(v_left_x3f_3946_);
v___x_3960_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3946_, v_startSize_3947_, v_startLhsPrec_3948_, v_startPos_3949_, v_prevPrio_3950_, v_snd_3958_, v_fn_3959_, v_a_3952_, v_a_3953_);
v_fst_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_fst_3961_);
v_snd_3962_ = lean_ctor_get(v___x_3960_, 1);
lean_inc(v_snd_3962_);
lean_dec_ref(v___x_3960_);
v_prevPrio_3950_ = v_snd_3962_;
v_ps_3951_ = v_tail_3957_;
v_a_3953_ = v_fst_3961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3964_, lean_object* v_startSize_3965_, lean_object* v_startLhsPrec_3966_, lean_object* v_startPos_3967_, lean_object* v_prevPrio_3968_, lean_object* v_ps_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3964_, v_startSize_3965_, v_startLhsPrec_3966_, v_startPos_3967_, v_prevPrio_3968_, v_ps_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_startSize_3965_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3973_, lean_object* v_startSize_3974_, lean_object* v_startLhsPrec_3975_, lean_object* v_startPos_3976_, lean_object* v_prevPrio_3977_, lean_object* v_ps_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3973_, v_startSize_3974_, v_startLhsPrec_3975_, v_startPos_3976_, v_prevPrio_3977_, v_ps_3978_, v_a_3979_, v_a_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3982_, lean_object* v_startSize_3983_, lean_object* v_startLhsPrec_3984_, lean_object* v_startPos_3985_, lean_object* v_prevPrio_3986_, lean_object* v_ps_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3982_, v_startSize_3983_, v_startLhsPrec_3984_, v_startPos_3985_, v_prevPrio_3986_, v_ps_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_startSize_3983_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3992_, lean_object* v_x_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
if (lean_obj_tag(v_x_3993_) == 0)
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_dec_ref(v_a_3994_);
lean_dec(v_left_x3f_3992_);
v___x_3996_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3997_ = l_Lean_Parser_ParserState_mkError(v_a_3995_, v___x_3996_);
return v___x_3997_;
}
else
{
lean_object* v_tail_3998_; 
v_tail_3998_ = lean_ctor_get(v_x_3993_, 1);
if (lean_obj_tag(v_tail_3998_) == 0)
{
lean_object* v_head_3999_; lean_object* v_fst_4000_; lean_object* v_lhsPrec_4001_; lean_object* v_fn_4002_; lean_object* v___x_4003_; 
v_head_3999_ = lean_ctor_get(v_x_3993_, 0);
lean_inc(v_head_3999_);
lean_dec_ref_known(v_x_3993_, 2);
v_fst_4000_ = lean_ctor_get(v_head_3999_, 0);
lean_inc(v_fst_4000_);
lean_dec(v_head_3999_);
v_lhsPrec_4001_ = lean_ctor_get(v_a_3995_, 1);
lean_inc(v_lhsPrec_4001_);
v_fn_4002_ = lean_ctor_get(v_fst_4000_, 1);
lean_inc_ref(v_fn_4002_);
lean_dec(v_fst_4000_);
v___x_4003_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3992_, v_lhsPrec_4001_, v_fn_4002_, v_a_3994_, v_a_3995_);
return v___x_4003_;
}
else
{
lean_object* v_head_4004_; lean_object* v_fst_4005_; lean_object* v_lhsPrec_4006_; lean_object* v_pos_4007_; lean_object* v_snd_4008_; lean_object* v_fn_4009_; lean_object* v_startSize_4010_; lean_object* v_s_4011_; lean_object* v___x_4012_; 
lean_inc(v_tail_3998_);
v_head_4004_ = lean_ctor_get(v_x_3993_, 0);
lean_inc(v_head_4004_);
lean_dec_ref_known(v_x_3993_, 2);
v_fst_4005_ = lean_ctor_get(v_head_4004_, 0);
lean_inc(v_fst_4005_);
v_lhsPrec_4006_ = lean_ctor_get(v_a_3995_, 1);
lean_inc_n(v_lhsPrec_4006_, 2);
v_pos_4007_ = lean_ctor_get(v_a_3995_, 2);
lean_inc(v_pos_4007_);
v_snd_4008_ = lean_ctor_get(v_head_4004_, 1);
lean_inc(v_snd_4008_);
lean_dec(v_head_4004_);
v_fn_4009_ = lean_ctor_get(v_fst_4005_, 1);
lean_inc_ref(v_fn_4009_);
lean_dec(v_fst_4005_);
v_startSize_4010_ = l_Lean_Parser_ParserState_stackSize(v_a_3995_);
lean_inc_ref(v_a_3994_);
lean_inc(v_left_x3f_3992_);
v_s_4011_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3992_, v_lhsPrec_4006_, v_fn_4009_, v_a_3994_, v_a_3995_);
v___x_4012_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3992_, v_startSize_4010_, v_lhsPrec_4006_, v_pos_4007_, v_snd_4008_, v_tail_3998_, v_a_3994_, v_s_4011_);
lean_dec(v_startSize_4010_);
return v___x_4012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_4014_, lean_object* v_x_4015_, lean_object* v_x_4016_){
_start:
{
if (lean_obj_tag(v_x_4014_) == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec_ref(v_x_4015_);
v___x_4017_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_4018_ = l_Lean_Parser_ParserState_mkError(v_x_4016_, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v_tail_4019_; 
v_tail_4019_ = lean_ctor_get(v_x_4014_, 1);
if (lean_obj_tag(v_tail_4019_) == 0)
{
lean_object* v_head_4020_; lean_object* v_fn_4021_; lean_object* v___x_4022_; 
v_head_4020_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_head_4020_);
lean_dec_ref_known(v_x_4014_, 2);
v_fn_4021_ = lean_ctor_get(v_head_4020_, 1);
lean_inc_ref(v_fn_4021_);
lean_dec(v_head_4020_);
v___x_4022_ = lean_apply_2(v_fn_4021_, v_x_4015_, v_x_4016_);
return v___x_4022_;
}
else
{
lean_object* v_head_4023_; lean_object* v_fn_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_inc(v_tail_4019_);
v_head_4023_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_head_4023_);
lean_dec_ref_known(v_x_4014_, 2);
v_fn_4024_ = lean_ctor_get(v_head_4023_, 1);
lean_inc_ref(v_fn_4024_);
lean_dec(v_head_4023_);
v___x_4025_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_4025_, 0, v_tail_4019_);
v___x_4026_ = l_Lean_Parser_orelseFn(v_fn_4024_, v___x_4025_, v_x_4015_, v_x_4016_);
return v___x_4026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_4027_, lean_object* v_c_4028_, lean_object* v_s_4029_){
_start:
{
lean_object* v_toCacheableParserContext_4030_; lean_object* v_savedPos_x3f_4031_; 
v_toCacheableParserContext_4030_ = lean_ctor_get(v_c_4028_, 2);
v_savedPos_x3f_4031_ = lean_ctor_get(v_toCacheableParserContext_4030_, 2);
lean_inc(v_savedPos_x3f_4031_);
if (lean_obj_tag(v_savedPos_x3f_4031_) == 0)
{
lean_dec_ref(v_c_4028_);
lean_dec_ref(v_errorMsg_4027_);
return v_s_4029_;
}
else
{
lean_object* v_toInputContext_4032_; lean_object* v_val_4033_; lean_object* v_fileMap_4034_; lean_object* v_pos_4035_; lean_object* v_savedPos_4036_; lean_object* v_pos_4037_; lean_object* v_column_4038_; lean_object* v_column_4039_; uint8_t v___x_4040_; 
v_toInputContext_4032_ = lean_ctor_get(v_c_4028_, 0);
lean_inc_ref(v_toInputContext_4032_);
lean_dec_ref(v_c_4028_);
v_val_4033_ = lean_ctor_get(v_savedPos_x3f_4031_, 0);
lean_inc(v_val_4033_);
lean_dec_ref_known(v_savedPos_x3f_4031_, 1);
v_fileMap_4034_ = lean_ctor_get(v_toInputContext_4032_, 2);
lean_inc_ref_n(v_fileMap_4034_, 2);
lean_dec_ref(v_toInputContext_4032_);
v_pos_4035_ = lean_ctor_get(v_s_4029_, 2);
v_savedPos_4036_ = l_Lean_FileMap_toPosition(v_fileMap_4034_, v_val_4033_);
lean_dec(v_val_4033_);
v_pos_4037_ = l_Lean_FileMap_toPosition(v_fileMap_4034_, v_pos_4035_);
v_column_4038_ = lean_ctor_get(v_pos_4037_, 1);
lean_inc(v_column_4038_);
lean_dec_ref(v_pos_4037_);
v_column_4039_ = lean_ctor_get(v_savedPos_4036_, 1);
lean_inc(v_column_4039_);
lean_dec_ref(v_savedPos_4036_);
v___x_4040_ = lean_nat_dec_eq(v_column_4038_, v_column_4039_);
lean_dec(v_column_4039_);
lean_dec(v_column_4038_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_Parser_ParserState_mkError(v_s_4029_, v_errorMsg_4027_);
return v___x_4041_;
}
else
{
lean_dec_ref(v_errorMsg_4027_);
return v_s_4029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_4042_){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4044_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_4044_, 0, v_errorMsg_4042_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4054_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4055_ = l_Lean_addBuiltinDocString(v___x_4053_, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4058_, lean_object* v_c_4059_, lean_object* v_s_4060_){
_start:
{
lean_object* v_toCacheableParserContext_4061_; lean_object* v_savedPos_x3f_4062_; 
v_toCacheableParserContext_4061_ = lean_ctor_get(v_c_4059_, 2);
v_savedPos_x3f_4062_ = lean_ctor_get(v_toCacheableParserContext_4061_, 2);
lean_inc(v_savedPos_x3f_4062_);
if (lean_obj_tag(v_savedPos_x3f_4062_) == 0)
{
lean_dec_ref(v_c_4059_);
lean_dec_ref(v_errorMsg_4058_);
return v_s_4060_;
}
else
{
lean_object* v_toInputContext_4063_; lean_object* v_val_4064_; lean_object* v_fileMap_4065_; lean_object* v_pos_4066_; lean_object* v_savedPos_4067_; lean_object* v_column_4068_; lean_object* v_pos_4069_; lean_object* v_column_4070_; uint8_t v___x_4071_; 
v_toInputContext_4063_ = lean_ctor_get(v_c_4059_, 0);
lean_inc_ref(v_toInputContext_4063_);
lean_dec_ref(v_c_4059_);
v_val_4064_ = lean_ctor_get(v_savedPos_x3f_4062_, 0);
lean_inc(v_val_4064_);
lean_dec_ref_known(v_savedPos_x3f_4062_, 1);
v_fileMap_4065_ = lean_ctor_get(v_toInputContext_4063_, 2);
lean_inc_ref_n(v_fileMap_4065_, 2);
lean_dec_ref(v_toInputContext_4063_);
v_pos_4066_ = lean_ctor_get(v_s_4060_, 2);
v_savedPos_4067_ = l_Lean_FileMap_toPosition(v_fileMap_4065_, v_val_4064_);
lean_dec(v_val_4064_);
v_column_4068_ = lean_ctor_get(v_savedPos_4067_, 1);
lean_inc(v_column_4068_);
lean_dec_ref(v_savedPos_4067_);
v_pos_4069_ = l_Lean_FileMap_toPosition(v_fileMap_4065_, v_pos_4066_);
v_column_4070_ = lean_ctor_get(v_pos_4069_, 1);
lean_inc(v_column_4070_);
lean_dec_ref(v_pos_4069_);
v___x_4071_ = lean_nat_dec_le(v_column_4068_, v_column_4070_);
lean_dec(v_column_4070_);
lean_dec(v_column_4068_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_Parser_ParserState_mkError(v_s_4060_, v_errorMsg_4058_);
return v___x_4072_;
}
else
{
lean_dec_ref(v_errorMsg_4058_);
return v_s_4060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4073_){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4075_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4075_, 0, v_errorMsg_4073_);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4074_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4085_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4086_ = l_Lean_addBuiltinDocString(v___x_4084_, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4089_, lean_object* v_c_4090_, lean_object* v_s_4091_){
_start:
{
lean_object* v_toCacheableParserContext_4092_; lean_object* v_savedPos_x3f_4093_; 
v_toCacheableParserContext_4092_ = lean_ctor_get(v_c_4090_, 2);
v_savedPos_x3f_4093_ = lean_ctor_get(v_toCacheableParserContext_4092_, 2);
lean_inc(v_savedPos_x3f_4093_);
if (lean_obj_tag(v_savedPos_x3f_4093_) == 0)
{
lean_dec_ref(v_c_4090_);
lean_dec_ref(v_errorMsg_4089_);
return v_s_4091_;
}
else
{
lean_object* v_toInputContext_4094_; lean_object* v_val_4095_; lean_object* v_fileMap_4096_; lean_object* v_pos_4097_; lean_object* v_savedPos_4098_; lean_object* v_column_4099_; lean_object* v_pos_4100_; lean_object* v_column_4101_; uint8_t v___x_4102_; 
v_toInputContext_4094_ = lean_ctor_get(v_c_4090_, 0);
lean_inc_ref(v_toInputContext_4094_);
lean_dec_ref(v_c_4090_);
v_val_4095_ = lean_ctor_get(v_savedPos_x3f_4093_, 0);
lean_inc(v_val_4095_);
lean_dec_ref_known(v_savedPos_x3f_4093_, 1);
v_fileMap_4096_ = lean_ctor_get(v_toInputContext_4094_, 2);
lean_inc_ref_n(v_fileMap_4096_, 2);
lean_dec_ref(v_toInputContext_4094_);
v_pos_4097_ = lean_ctor_get(v_s_4091_, 2);
v_savedPos_4098_ = l_Lean_FileMap_toPosition(v_fileMap_4096_, v_val_4095_);
lean_dec(v_val_4095_);
v_column_4099_ = lean_ctor_get(v_savedPos_4098_, 1);
lean_inc(v_column_4099_);
lean_dec_ref(v_savedPos_4098_);
v_pos_4100_ = l_Lean_FileMap_toPosition(v_fileMap_4096_, v_pos_4097_);
v_column_4101_ = lean_ctor_get(v_pos_4100_, 1);
lean_inc(v_column_4101_);
lean_dec_ref(v_pos_4100_);
v___x_4102_ = lean_nat_dec_lt(v_column_4099_, v_column_4101_);
lean_dec(v_column_4101_);
lean_dec(v_column_4099_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_Parser_ParserState_mkError(v_s_4091_, v_errorMsg_4089_);
return v___x_4103_;
}
else
{
lean_dec_ref(v_errorMsg_4089_);
return v_s_4091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4104_){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4105_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4106_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4106_, 0, v_errorMsg_4104_);
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4116_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4117_ = l_Lean_addBuiltinDocString(v___x_4115_, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4120_, lean_object* v_c_4121_, lean_object* v_s_4122_){
_start:
{
lean_object* v_toCacheableParserContext_4123_; lean_object* v_savedPos_x3f_4124_; 
v_toCacheableParserContext_4123_ = lean_ctor_get(v_c_4121_, 2);
v_savedPos_x3f_4124_ = lean_ctor_get(v_toCacheableParserContext_4123_, 2);
lean_inc(v_savedPos_x3f_4124_);
if (lean_obj_tag(v_savedPos_x3f_4124_) == 0)
{
lean_dec_ref(v_c_4121_);
lean_dec_ref(v_errorMsg_4120_);
return v_s_4122_;
}
else
{
lean_object* v_toInputContext_4125_; lean_object* v_val_4126_; lean_object* v_fileMap_4127_; lean_object* v_pos_4128_; lean_object* v_savedPos_4129_; lean_object* v_pos_4130_; lean_object* v_line_4131_; lean_object* v_line_4132_; uint8_t v___x_4133_; 
v_toInputContext_4125_ = lean_ctor_get(v_c_4121_, 0);
lean_inc_ref(v_toInputContext_4125_);
lean_dec_ref(v_c_4121_);
v_val_4126_ = lean_ctor_get(v_savedPos_x3f_4124_, 0);
lean_inc(v_val_4126_);
lean_dec_ref_known(v_savedPos_x3f_4124_, 1);
v_fileMap_4127_ = lean_ctor_get(v_toInputContext_4125_, 2);
lean_inc_ref_n(v_fileMap_4127_, 2);
lean_dec_ref(v_toInputContext_4125_);
v_pos_4128_ = lean_ctor_get(v_s_4122_, 2);
v_savedPos_4129_ = l_Lean_FileMap_toPosition(v_fileMap_4127_, v_val_4126_);
lean_dec(v_val_4126_);
v_pos_4130_ = l_Lean_FileMap_toPosition(v_fileMap_4127_, v_pos_4128_);
v_line_4131_ = lean_ctor_get(v_pos_4130_, 0);
lean_inc(v_line_4131_);
lean_dec_ref(v_pos_4130_);
v_line_4132_ = lean_ctor_get(v_savedPos_4129_, 0);
lean_inc(v_line_4132_);
lean_dec_ref(v_savedPos_4129_);
v___x_4133_ = lean_nat_dec_eq(v_line_4131_, v_line_4132_);
lean_dec(v_line_4132_);
lean_dec(v_line_4131_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_Parser_ParserState_mkError(v_s_4122_, v_errorMsg_4120_);
return v___x_4134_;
}
else
{
lean_dec_ref(v_errorMsg_4120_);
return v_s_4122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4135_){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4137_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4137_, 0, v_errorMsg_4135_);
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4147_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4148_ = l_Lean_addBuiltinDocString(v___x_4146_, v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4151_, lean_object* v_x_4152_){
_start:
{
lean_object* v_prec_4153_; lean_object* v_quotDepth_4154_; uint8_t v_suppressInsideQuot_4155_; lean_object* v_forbiddenTks_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4165_; 
v_prec_4153_ = lean_ctor_get(v_x_4152_, 0);
v_quotDepth_4154_ = lean_ctor_get(v_x_4152_, 1);
v_suppressInsideQuot_4155_ = lean_ctor_get_uint8(v_x_4152_, sizeof(void*)*4);
v_forbiddenTks_4156_ = lean_ctor_get(v_x_4152_, 3);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_x_4152_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v_x_4152_, 2);
lean_dec(v_unused_4166_);
v___x_4158_ = v_x_4152_;
v_isShared_4159_ = v_isSharedCheck_4165_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_forbiddenTks_4156_);
lean_inc(v_quotDepth_4154_);
lean_inc(v_prec_4153_);
lean_dec(v_x_4152_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4165_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_pos_4160_; lean_object* v___x_4161_; lean_object* v___x_4163_; 
v_pos_4160_ = lean_ctor_get(v___y_4151_, 2);
lean_inc(v_pos_4160_);
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_pos_4160_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 2, v___x_4161_);
v___x_4163_ = v___x_4158_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_prec_4153_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v_quotDepth_4154_);
lean_ctor_set(v_reuseFailAlloc_4164_, 2, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4164_, 3, v_forbiddenTks_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4164_, sizeof(void*)*4, v_suppressInsideQuot_4155_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4167_, lean_object* v_x_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Parser_withPosition___lam__0(v___y_4167_, v_x_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v___f_4173_; lean_object* v___x_4174_; 
lean_inc_ref(v___y_4172_);
v___f_4173_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4173_, 0, v___y_4172_);
v___x_4174_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4173_, v_fn_4170_, v___y_4171_, v___y_4172_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4175_){
_start:
{
lean_object* v_info_4176_; lean_object* v_fn_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4185_; 
v_info_4176_ = lean_ctor_get(v_p_4175_, 0);
v_fn_4177_ = lean_ctor_get(v_p_4175_, 1);
v_isSharedCheck_4185_ = !lean_is_exclusive(v_p_4175_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4179_ = v_p_4175_;
v_isShared_4180_ = v_isSharedCheck_4185_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_fn_4177_);
lean_inc(v_info_4176_);
lean_dec(v_p_4175_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4185_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___f_4181_; lean_object* v___x_4183_; 
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4181_, 0, v_fn_4177_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___f_4181_);
v___x_4183_ = v___x_4179_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_info_4176_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v___f_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4193_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4194_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4195_ = l_Lean_addBuiltinDocString(v___x_4193_, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4198_, lean_object* v_pos_4199_, lean_object* v_c_4200_){
_start:
{
uint8_t v___x_4201_; 
v___x_4201_ = l_Lean_Parser_checkTailLinebreak(v_prev_4198_);
if (v___x_4201_ == 0)
{
lean_dec(v_pos_4199_);
return v_c_4200_;
}
else
{
lean_object* v_prec_4202_; lean_object* v_quotDepth_4203_; uint8_t v_suppressInsideQuot_4204_; lean_object* v_forbiddenTks_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4213_; 
v_prec_4202_ = lean_ctor_get(v_c_4200_, 0);
v_quotDepth_4203_ = lean_ctor_get(v_c_4200_, 1);
v_suppressInsideQuot_4204_ = lean_ctor_get_uint8(v_c_4200_, sizeof(void*)*4);
v_forbiddenTks_4205_ = lean_ctor_get(v_c_4200_, 3);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_c_4200_);
if (v_isSharedCheck_4213_ == 0)
{
lean_object* v_unused_4214_; 
v_unused_4214_ = lean_ctor_get(v_c_4200_, 2);
lean_dec(v_unused_4214_);
v___x_4207_ = v_c_4200_;
v_isShared_4208_ = v_isSharedCheck_4213_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_forbiddenTks_4205_);
lean_inc(v_quotDepth_4203_);
lean_inc(v_prec_4202_);
lean_dec(v_c_4200_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4213_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_pos_4199_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 2, v___x_4209_);
v___x_4211_ = v___x_4207_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_prec_4202_);
lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_quotDepth_4203_);
lean_ctor_set(v_reuseFailAlloc_4212_, 2, v___x_4209_);
lean_ctor_set(v_reuseFailAlloc_4212_, 3, v_forbiddenTks_4205_);
lean_ctor_set_uint8(v_reuseFailAlloc_4212_, sizeof(void*)*4, v_suppressInsideQuot_4204_);
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
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4215_, lean_object* v_pos_4216_, lean_object* v_c_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4215_, v_pos_4216_, v_c_4217_);
lean_dec(v_prev_4215_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_stxStack_4222_; lean_object* v_pos_4223_; lean_object* v_prev_4224_; lean_object* v___f_4225_; lean_object* v___x_4226_; 
v_stxStack_4222_ = lean_ctor_get(v___y_4221_, 0);
v_pos_4223_ = lean_ctor_get(v___y_4221_, 2);
v_prev_4224_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4222_);
lean_inc(v_pos_4223_);
v___f_4225_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4225_, 0, v_prev_4224_);
lean_closure_set(v___f_4225_, 1, v_pos_4223_);
v___x_4226_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4225_, v_fn_4219_, v___y_4220_, v___y_4221_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4227_){
_start:
{
lean_object* v_info_4228_; lean_object* v_fn_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4237_; 
v_info_4228_ = lean_ctor_get(v_p_4227_, 0);
v_fn_4229_ = lean_ctor_get(v_p_4227_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_p_4227_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4231_ = v_p_4227_;
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_fn_4229_);
lean_inc(v_info_4228_);
lean_dec(v_p_4227_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___f_4233_; lean_object* v___x_4235_; 
v___f_4233_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4233_, 0, v_fn_4229_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 1, v___f_4233_);
v___x_4235_ = v___x_4231_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_info_4228_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___f_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4238_){
_start:
{
lean_object* v_prec_4239_; lean_object* v_quotDepth_4240_; uint8_t v_suppressInsideQuot_4241_; lean_object* v_forbiddenTks_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4250_; 
v_prec_4239_ = lean_ctor_get(v_x_4238_, 0);
v_quotDepth_4240_ = lean_ctor_get(v_x_4238_, 1);
v_suppressInsideQuot_4241_ = lean_ctor_get_uint8(v_x_4238_, sizeof(void*)*4);
v_forbiddenTks_4242_ = lean_ctor_get(v_x_4238_, 3);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_x_4238_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v_x_4238_, 2);
lean_dec(v_unused_4251_);
v___x_4244_ = v_x_4238_;
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_forbiddenTks_4242_);
lean_inc(v_quotDepth_4240_);
lean_inc(v_prec_4239_);
lean_dec(v_x_4238_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4246_ = lean_box(0);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 2, v___x_4246_);
v___x_4248_ = v___x_4244_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_prec_4239_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_quotDepth_4240_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v_forbiddenTks_4242_);
lean_ctor_set_uint8(v_reuseFailAlloc_4249_, sizeof(void*)*4, v_suppressInsideQuot_4241_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4253_){
_start:
{
lean_object* v___f_4254_; lean_object* v___x_4255_; 
v___f_4254_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4255_ = l_Lean_Parser_adaptCacheableContext(v___f_4254_, v_p_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4264_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4265_ = l_Lean_addBuiltinDocString(v___x_4263_, v___x_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4268_, lean_object* v_c_4269_){
_start:
{
lean_object* v_prec_4270_; lean_object* v_quotDepth_4271_; uint8_t v_suppressInsideQuot_4272_; lean_object* v_savedPos_x3f_4273_; lean_object* v_forbiddenTks_4274_; uint8_t v___x_4275_; 
v_prec_4270_ = lean_ctor_get(v_c_4269_, 0);
v_quotDepth_4271_ = lean_ctor_get(v_c_4269_, 1);
v_suppressInsideQuot_4272_ = lean_ctor_get_uint8(v_c_4269_, sizeof(void*)*4);
v_savedPos_x3f_4273_ = lean_ctor_get(v_c_4269_, 2);
v_forbiddenTks_4274_ = lean_ctor_get(v_c_4269_, 3);
v___x_4275_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_4274_, v_tk_4268_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4283_; 
lean_inc_ref(v_forbiddenTks_4274_);
lean_inc(v_savedPos_x3f_4273_);
lean_inc(v_quotDepth_4271_);
lean_inc(v_prec_4270_);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_c_4269_);
if (v_isSharedCheck_4283_ == 0)
{
lean_object* v_unused_4284_; lean_object* v_unused_4285_; lean_object* v_unused_4286_; lean_object* v_unused_4287_; 
v_unused_4284_ = lean_ctor_get(v_c_4269_, 3);
lean_dec(v_unused_4284_);
v_unused_4285_ = lean_ctor_get(v_c_4269_, 2);
lean_dec(v_unused_4285_);
v_unused_4286_ = lean_ctor_get(v_c_4269_, 1);
lean_dec(v_unused_4286_);
v_unused_4287_ = lean_ctor_get(v_c_4269_, 0);
lean_dec(v_unused_4287_);
v___x_4277_ = v_c_4269_;
v_isShared_4278_ = v_isSharedCheck_4283_;
goto v_resetjp_4276_;
}
else
{
lean_dec(v_c_4269_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4283_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4279_; lean_object* v___x_4281_; 
v___x_4279_ = lean_array_push(v_forbiddenTks_4274_, v_tk_4268_);
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 3, v___x_4279_);
v___x_4281_ = v___x_4277_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_prec_4270_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_quotDepth_4271_);
lean_ctor_set(v_reuseFailAlloc_4282_, 2, v_savedPos_x3f_4273_);
lean_ctor_set(v_reuseFailAlloc_4282_, 3, v___x_4279_);
lean_ctor_set_uint8(v_reuseFailAlloc_4282_, sizeof(void*)*4, v_suppressInsideQuot_4272_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
else
{
lean_dec_ref(v_tk_4268_);
return v_c_4269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4288_, lean_object* v_p_4289_){
_start:
{
lean_object* v___f_4290_; lean_object* v___x_4291_; 
v___f_4290_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4290_, 0, v_tk_4288_);
v___x_4291_ = l_Lean_Parser_adaptCacheableContext(v___f_4290_, v_p_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4300_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4301_ = l_Lean_addBuiltinDocString(v___x_4299_, v___x_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4303_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(lean_object* v_a_4304_, lean_object* v_as_4305_, size_t v_i_4306_, size_t v_stop_4307_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_usize_dec_eq(v_i_4306_, v_stop_4307_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4309_ = lean_array_uget_borrowed(v_as_4305_, v_i_4306_);
v___x_4310_ = lean_string_dec_eq(v___x_4309_, v_a_4304_);
if (v___x_4310_ == 0)
{
size_t v___x_4311_; size_t v___x_4312_; 
v___x_4311_ = ((size_t)1ULL);
v___x_4312_ = lean_usize_add(v_i_4306_, v___x_4311_);
v_i_4306_ = v___x_4312_;
goto _start;
}
else
{
return v___x_4310_;
}
}
else
{
uint8_t v___x_4314_; 
v___x_4314_ = 0;
return v___x_4314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0___boxed(lean_object* v_a_4315_, lean_object* v_as_4316_, lean_object* v_i_4317_, lean_object* v_stop_4318_){
_start:
{
size_t v_i_boxed_4319_; size_t v_stop_boxed_4320_; uint8_t v_res_4321_; lean_object* v_r_4322_; 
v_i_boxed_4319_ = lean_unbox_usize(v_i_4317_);
lean_dec(v_i_4317_);
v_stop_boxed_4320_ = lean_unbox_usize(v_stop_4318_);
lean_dec(v_stop_4318_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4315_, v_as_4316_, v_i_boxed_4319_, v_stop_boxed_4320_);
lean_dec_ref(v_as_4316_);
lean_dec_ref(v_a_4315_);
v_r_4322_ = lean_box(v_res_4321_);
return v_r_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(lean_object* v_size_4323_, lean_object* v_as_4324_, size_t v_sz_4325_, size_t v_i_4326_, lean_object* v_b_4327_){
_start:
{
lean_object* v_a_4329_; uint8_t v___x_4333_; 
v___x_4333_ = lean_usize_dec_lt(v_i_4326_, v_sz_4325_);
if (v___x_4333_ == 0)
{
lean_dec(v_size_4323_);
return v_b_4327_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4337_; lean_object* v___y_4339_; uint8_t v___x_4344_; 
v_a_4334_ = lean_array_uget_borrowed(v_as_4324_, v_i_4326_);
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4344_ = lean_nat_dec_lt(v___x_4337_, v_size_4323_);
if (v___x_4344_ == 0)
{
goto v___jp_4335_;
}
else
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = lean_array_get_size(v_b_4327_);
v___x_4346_ = lean_nat_dec_le(v_size_4323_, v___x_4345_);
if (v___x_4346_ == 0)
{
v___y_4339_ = v___x_4345_;
goto v___jp_4338_;
}
else
{
lean_inc(v_size_4323_);
v___y_4339_ = v_size_4323_;
goto v___jp_4338_;
}
}
v___jp_4335_:
{
lean_object* v___x_4336_; 
lean_inc(v_a_4334_);
v___x_4336_ = lean_array_push(v_b_4327_, v_a_4334_);
v_a_4329_ = v___x_4336_;
goto v___jp_4328_;
}
v___jp_4338_:
{
uint8_t v___x_4340_; 
v___x_4340_ = lean_nat_dec_lt(v___x_4337_, v___y_4339_);
if (v___x_4340_ == 0)
{
lean_dec(v___y_4339_);
goto v___jp_4335_;
}
else
{
size_t v___x_4341_; size_t v___x_4342_; uint8_t v___x_4343_; 
v___x_4341_ = ((size_t)0ULL);
v___x_4342_ = lean_usize_of_nat(v___y_4339_);
lean_dec(v___y_4339_);
v___x_4343_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4334_, v_b_4327_, v___x_4341_, v___x_4342_);
if (v___x_4343_ == 0)
{
goto v___jp_4335_;
}
else
{
v_a_4329_ = v_b_4327_;
goto v___jp_4328_;
}
}
}
}
v___jp_4328_:
{
size_t v___x_4330_; size_t v___x_4331_; 
v___x_4330_ = ((size_t)1ULL);
v___x_4331_ = lean_usize_add(v_i_4326_, v___x_4330_);
v_i_4326_ = v___x_4331_;
v_b_4327_ = v_a_4329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1___boxed(lean_object* v_size_4347_, lean_object* v_as_4348_, lean_object* v_sz_4349_, lean_object* v_i_4350_, lean_object* v_b_4351_){
_start:
{
size_t v_sz_boxed_4352_; size_t v_i_boxed_4353_; lean_object* v_res_4354_; 
v_sz_boxed_4352_ = lean_unbox_usize(v_sz_4349_);
lean_dec(v_sz_4349_);
v_i_boxed_4353_ = lean_unbox_usize(v_i_4350_);
lean_dec(v_i_4350_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4347_, v_as_4348_, v_sz_boxed_4352_, v_i_boxed_4353_, v_b_4351_);
lean_dec_ref(v_as_4348_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(lean_object* v_init_4355_, lean_object* v_tks_4356_){
_start:
{
lean_object* v_size_4357_; size_t v_sz_4358_; size_t v___x_4359_; lean_object* v___x_4360_; 
v_size_4357_ = lean_array_get_size(v_init_4355_);
v_sz_4358_ = lean_array_size(v_tks_4356_);
v___x_4359_ = ((size_t)0ULL);
v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4357_, v_tks_4356_, v_sz_4358_, v___x_4359_, v_init_4355_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks___boxed(lean_object* v_init_4361_, lean_object* v_tks_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_init_4361_, v_tks_4362_);
lean_dec_ref(v_tks_4362_);
return v_res_4363_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__6));
v___x_4386_ = l_Lean_mkAtom(v___x_4385_);
return v___x_4386_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4387_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__8, &l_Lean_Parser_withForbiddens___auto__1___closed__8_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__8);
v___x_4388_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4389_ = lean_array_push(v___x_4388_, v___x_4387_);
return v___x_4389_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4400_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_4401_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4402_ = lean_array_push(v___x_4401_, v___x_4400_);
return v___x_4402_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4403_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__13, &l_Lean_Parser_withForbiddens___auto__1___closed__13_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__13);
v___x_4404_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__11));
v___x_4405_ = lean_box(2);
v___x_4406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
lean_ctor_set(v___x_4406_, 1, v___x_4404_);
lean_ctor_set(v___x_4406_, 2, v___x_4403_);
return v___x_4406_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4407_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__14, &l_Lean_Parser_withForbiddens___auto__1___closed__14_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__14);
v___x_4408_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__9, &l_Lean_Parser_withForbiddens___auto__1___closed__9_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__9);
v___x_4409_ = lean_array_push(v___x_4408_, v___x_4407_);
return v___x_4409_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4410_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__15, &l_Lean_Parser_withForbiddens___auto__1___closed__15_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__15);
v___x_4411_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__7));
v___x_4412_ = lean_box(2);
v___x_4413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v___x_4411_);
lean_ctor_set(v___x_4413_, 2, v___x_4410_);
return v___x_4413_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__16, &l_Lean_Parser_withForbiddens___auto__1___closed__16_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__16);
v___x_4415_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4416_ = lean_array_push(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4417_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__17, &l_Lean_Parser_withForbiddens___auto__1___closed__17_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__17);
v___x_4418_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_4419_ = lean_box(2);
v___x_4420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
lean_ctor_set(v___x_4420_, 1, v___x_4418_);
lean_ctor_set(v___x_4420_, 2, v___x_4417_);
return v___x_4420_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4421_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__18, &l_Lean_Parser_withForbiddens___auto__1___closed__18_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__18);
v___x_4422_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4423_ = lean_array_push(v___x_4422_, v___x_4421_);
return v___x_4423_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4424_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__19, &l_Lean_Parser_withForbiddens___auto__1___closed__19_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__19);
v___x_4425_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__5));
v___x_4426_ = lean_box(2);
v___x_4427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
lean_ctor_set(v___x_4427_, 1, v___x_4425_);
lean_ctor_set(v___x_4427_, 2, v___x_4424_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__20, &l_Lean_Parser_withForbiddens___auto__1___closed__20_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__20);
v___x_4429_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4430_ = lean_array_push(v___x_4429_, v___x_4428_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4431_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__21, &l_Lean_Parser_withForbiddens___auto__1___closed__21_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__21);
v___x_4432_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__2));
v___x_4433_ = lean_box(2);
v___x_4434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
lean_ctor_set(v___x_4434_, 1, v___x_4432_);
lean_ctor_set(v___x_4434_, 2, v___x_4431_);
return v___x_4434_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1(void){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__22, &l_Lean_Parser_withForbiddens___auto__1___closed__22_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__22);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg___lam__0(lean_object* v_tks_4436_, lean_object* v_c_4437_){
_start:
{
lean_object* v_prec_4438_; lean_object* v_quotDepth_4439_; uint8_t v_suppressInsideQuot_4440_; lean_object* v_savedPos_x3f_4441_; lean_object* v_forbiddenTks_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4456_; 
v_prec_4438_ = lean_ctor_get(v_c_4437_, 0);
v_quotDepth_4439_ = lean_ctor_get(v_c_4437_, 1);
v_suppressInsideQuot_4440_ = lean_ctor_get_uint8(v_c_4437_, sizeof(void*)*4);
v_savedPos_x3f_4441_ = lean_ctor_get(v_c_4437_, 2);
v_forbiddenTks_4442_ = lean_ctor_get(v_c_4437_, 3);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_c_4437_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4444_ = v_c_4437_;
v_isShared_4445_ = v_isSharedCheck_4456_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_forbiddenTks_4442_);
lean_inc(v_savedPos_x3f_4441_);
lean_inc(v_quotDepth_4439_);
lean_inc(v_prec_4438_);
lean_dec(v_c_4437_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4456_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4446_ = lean_array_get_size(v_forbiddenTks_4442_);
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = lean_nat_dec_eq(v___x_4446_, v___x_4447_);
if (v___x_4448_ == 0)
{
lean_object* v___x_4449_; lean_object* v___x_4451_; 
v___x_4449_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_forbiddenTks_4442_, v_tks_4436_);
lean_dec_ref(v_tks_4436_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 3, v___x_4449_);
v___x_4451_ = v___x_4444_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_prec_4438_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_quotDepth_4439_);
lean_ctor_set(v_reuseFailAlloc_4452_, 2, v_savedPos_x3f_4441_);
lean_ctor_set(v_reuseFailAlloc_4452_, 3, v___x_4449_);
lean_ctor_set_uint8(v_reuseFailAlloc_4452_, sizeof(void*)*4, v_suppressInsideQuot_4440_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
else
{
lean_object* v___x_4454_; 
lean_dec_ref(v_forbiddenTks_4442_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 3, v_tks_4436_);
v___x_4454_ = v___x_4444_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_prec_4438_);
lean_ctor_set(v_reuseFailAlloc_4455_, 1, v_quotDepth_4439_);
lean_ctor_set(v_reuseFailAlloc_4455_, 2, v_savedPos_x3f_4441_);
lean_ctor_set(v_reuseFailAlloc_4455_, 3, v_tks_4436_);
lean_ctor_set_uint8(v_reuseFailAlloc_4455_, sizeof(void*)*4, v_suppressInsideQuot_4440_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg(lean_object* v_tks_4457_, lean_object* v_p_4458_){
_start:
{
lean_object* v___f_4459_; lean_object* v___x_4460_; 
v___f_4459_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbiddens___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4459_, 0, v_tks_4457_);
v___x_4460_ = l_Lean_Parser_adaptCacheableContext(v___f_4459_, v_p_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens(lean_object* v_tks_4461_, lean_object* v_p_4462_, lean_object* v___h_4463_){
_start:
{
lean_object* v___x_4464_; 
v___x_4464_ = l_Lean_Parser_withForbiddens___redArg(v_tks_4461_, v_p_4462_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1(){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1));
v___x_4473_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2));
v___x_4474_ = l_Lean_addBuiltinDocString(v___x_4472_, v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___boxed(lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4479_){
_start:
{
lean_object* v_prec_4480_; lean_object* v_quotDepth_4481_; uint8_t v_suppressInsideQuot_4482_; lean_object* v_savedPos_x3f_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4491_; 
v_prec_4480_ = lean_ctor_get(v_x_4479_, 0);
v_quotDepth_4481_ = lean_ctor_get(v_x_4479_, 1);
v_suppressInsideQuot_4482_ = lean_ctor_get_uint8(v_x_4479_, sizeof(void*)*4);
v_savedPos_x3f_4483_ = lean_ctor_get(v_x_4479_, 2);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_x_4479_);
if (v_isSharedCheck_4491_ == 0)
{
lean_object* v_unused_4492_; 
v_unused_4492_ = lean_ctor_get(v_x_4479_, 3);
lean_dec(v_unused_4492_);
v___x_4485_ = v_x_4479_;
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_savedPos_x3f_4483_);
lean_inc(v_quotDepth_4481_);
lean_inc(v_prec_4480_);
lean_dec(v_x_4479_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___lam__0___closed__0));
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 3, v___x_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_prec_4480_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_quotDepth_4481_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_savedPos_x3f_4483_);
lean_ctor_set(v_reuseFailAlloc_4490_, 3, v___x_4487_);
lean_ctor_set_uint8(v_reuseFailAlloc_4490_, sizeof(void*)*4, v_suppressInsideQuot_4482_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4494_){
_start:
{
lean_object* v___f_4495_; lean_object* v___x_4496_; 
v___f_4495_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4496_ = l_Lean_Parser_adaptCacheableContext(v___f_4495_, v_p_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4505_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4506_ = l_Lean_addBuiltinDocString(v___x_4504_, v___x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4510_, lean_object* v_s_4511_){
_start:
{
lean_object* v_pos_4512_; lean_object* v_toInputContext_4513_; uint8_t v___x_4514_; 
v_pos_4512_ = lean_ctor_get(v_s_4511_, 2);
v_toInputContext_4513_ = lean_ctor_get(v_c_4510_, 0);
v___x_4514_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4513_, v_pos_4512_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4516_ = l_Lean_Parser_ParserState_mkError(v_s_4511_, v___x_4515_);
return v___x_4516_;
}
else
{
return v_s_4511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4517_, lean_object* v_s_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_Parser_eoiFn(v_c_4517_, v_s_4518_);
lean_dec_ref(v_c_4517_);
return v_res_4519_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4521_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v___x_4520_);
return v___x_4522_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4524_, lean_object* v_v_4525_, lean_object* v_t_4526_){
_start:
{
if (lean_obj_tag(v_t_4526_) == 0)
{
lean_object* v_size_4527_; lean_object* v_k_4528_; lean_object* v_v_4529_; lean_object* v_l_4530_; lean_object* v_r_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4811_; 
v_size_4527_ = lean_ctor_get(v_t_4526_, 0);
v_k_4528_ = lean_ctor_get(v_t_4526_, 1);
v_v_4529_ = lean_ctor_get(v_t_4526_, 2);
v_l_4530_ = lean_ctor_get(v_t_4526_, 3);
v_r_4531_ = lean_ctor_get(v_t_4526_, 4);
v_isSharedCheck_4811_ = !lean_is_exclusive(v_t_4526_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4533_ = v_t_4526_;
v_isShared_4534_ = v_isSharedCheck_4811_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_r_4531_);
lean_inc(v_l_4530_);
lean_inc(v_v_4529_);
lean_inc(v_k_4528_);
lean_inc(v_size_4527_);
lean_dec(v_t_4526_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4811_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
uint8_t v___x_4535_; 
v___x_4535_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4524_, v_k_4528_);
switch(v___x_4535_)
{
case 0:
{
lean_object* v_impl_4536_; lean_object* v___x_4537_; 
lean_dec(v_size_4527_);
v_impl_4536_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4524_, v_v_4525_, v_l_4530_);
v___x_4537_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4531_) == 0)
{
lean_object* v_size_4538_; lean_object* v_size_4539_; lean_object* v_k_4540_; lean_object* v_v_4541_; lean_object* v_l_4542_; lean_object* v_r_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; uint8_t v___x_4546_; 
v_size_4538_ = lean_ctor_get(v_r_4531_, 0);
v_size_4539_ = lean_ctor_get(v_impl_4536_, 0);
lean_inc(v_size_4539_);
v_k_4540_ = lean_ctor_get(v_impl_4536_, 1);
lean_inc(v_k_4540_);
v_v_4541_ = lean_ctor_get(v_impl_4536_, 2);
lean_inc(v_v_4541_);
v_l_4542_ = lean_ctor_get(v_impl_4536_, 3);
lean_inc(v_l_4542_);
v_r_4543_ = lean_ctor_get(v_impl_4536_, 4);
lean_inc(v_r_4543_);
v___x_4544_ = lean_unsigned_to_nat(3u);
v___x_4545_ = lean_nat_mul(v___x_4544_, v_size_4538_);
v___x_4546_ = lean_nat_dec_lt(v___x_4545_, v_size_4539_);
lean_dec(v___x_4545_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
lean_dec(v_r_4543_);
lean_dec(v_l_4542_);
lean_dec(v_v_4541_);
lean_dec(v_k_4540_);
v___x_4547_ = lean_nat_add(v___x_4537_, v_size_4539_);
lean_dec(v_size_4539_);
v___x_4548_ = lean_nat_add(v___x_4547_, v_size_4538_);
lean_dec(v___x_4547_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 3, v_impl_4536_);
lean_ctor_set(v___x_4533_, 0, v___x_4548_);
v___x_4550_ = v___x_4533_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4551_, 3, v_impl_4536_);
lean_ctor_set(v_reuseFailAlloc_4551_, 4, v_r_4531_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
else
{
lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4617_; 
v_isSharedCheck_4617_ = !lean_is_exclusive(v_impl_4536_);
if (v_isSharedCheck_4617_ == 0)
{
lean_object* v_unused_4618_; lean_object* v_unused_4619_; lean_object* v_unused_4620_; lean_object* v_unused_4621_; lean_object* v_unused_4622_; 
v_unused_4618_ = lean_ctor_get(v_impl_4536_, 4);
lean_dec(v_unused_4618_);
v_unused_4619_ = lean_ctor_get(v_impl_4536_, 3);
lean_dec(v_unused_4619_);
v_unused_4620_ = lean_ctor_get(v_impl_4536_, 2);
lean_dec(v_unused_4620_);
v_unused_4621_ = lean_ctor_get(v_impl_4536_, 1);
lean_dec(v_unused_4621_);
v_unused_4622_ = lean_ctor_get(v_impl_4536_, 0);
lean_dec(v_unused_4622_);
v___x_4553_ = v_impl_4536_;
v_isShared_4554_ = v_isSharedCheck_4617_;
goto v_resetjp_4552_;
}
else
{
lean_dec(v_impl_4536_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4617_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v_size_4555_; lean_object* v_size_4556_; lean_object* v_k_4557_; lean_object* v_v_4558_; lean_object* v_l_4559_; lean_object* v_r_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_size_4555_ = lean_ctor_get(v_l_4542_, 0);
v_size_4556_ = lean_ctor_get(v_r_4543_, 0);
v_k_4557_ = lean_ctor_get(v_r_4543_, 1);
v_v_4558_ = lean_ctor_get(v_r_4543_, 2);
v_l_4559_ = lean_ctor_get(v_r_4543_, 3);
v_r_4560_ = lean_ctor_get(v_r_4543_, 4);
v___x_4561_ = lean_unsigned_to_nat(2u);
v___x_4562_ = lean_nat_mul(v___x_4561_, v_size_4555_);
v___x_4563_ = lean_nat_dec_lt(v_size_4556_, v___x_4562_);
lean_dec(v___x_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4592_; 
lean_inc(v_r_4560_);
lean_inc(v_l_4559_);
lean_inc(v_v_4558_);
lean_inc(v_k_4557_);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_r_4543_);
if (v_isSharedCheck_4592_ == 0)
{
lean_object* v_unused_4593_; lean_object* v_unused_4594_; lean_object* v_unused_4595_; lean_object* v_unused_4596_; lean_object* v_unused_4597_; 
v_unused_4593_ = lean_ctor_get(v_r_4543_, 4);
lean_dec(v_unused_4593_);
v_unused_4594_ = lean_ctor_get(v_r_4543_, 3);
lean_dec(v_unused_4594_);
v_unused_4595_ = lean_ctor_get(v_r_4543_, 2);
lean_dec(v_unused_4595_);
v_unused_4596_ = lean_ctor_get(v_r_4543_, 1);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_r_4543_, 0);
lean_dec(v_unused_4597_);
v___x_4565_ = v_r_4543_;
v_isShared_4566_ = v_isSharedCheck_4592_;
goto v_resetjp_4564_;
}
else
{
lean_dec(v_r_4543_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4592_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___x_4580_; lean_object* v___y_4582_; 
v___x_4567_ = lean_nat_add(v___x_4537_, v_size_4539_);
lean_dec(v_size_4539_);
v___x_4568_ = lean_nat_add(v___x_4567_, v_size_4538_);
lean_dec(v___x_4567_);
v___x_4580_ = lean_nat_add(v___x_4537_, v_size_4555_);
if (lean_obj_tag(v_l_4559_) == 0)
{
lean_object* v_size_4590_; 
v_size_4590_ = lean_ctor_get(v_l_4559_, 0);
lean_inc(v_size_4590_);
v___y_4582_ = v_size_4590_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_unsigned_to_nat(0u);
v___y_4582_ = v___x_4591_;
goto v___jp_4581_;
}
v___jp_4569_:
{
lean_object* v___x_4573_; lean_object* v___x_4575_; 
v___x_4573_ = lean_nat_add(v___y_4570_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 4, v_r_4531_);
lean_ctor_set(v___x_4565_, 3, v_r_4560_);
lean_ctor_set(v___x_4565_, 2, v_v_4529_);
lean_ctor_set(v___x_4565_, 1, v_k_4528_);
lean_ctor_set(v___x_4565_, 0, v___x_4573_);
v___x_4575_ = v___x_4565_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4573_);
lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4579_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4579_, 3, v_r_4560_);
lean_ctor_set(v_reuseFailAlloc_4579_, 4, v_r_4531_);
v___x_4575_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
lean_object* v___x_4577_; 
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 4, v___x_4575_);
lean_ctor_set(v___x_4553_, 3, v___y_4571_);
lean_ctor_set(v___x_4553_, 2, v_v_4558_);
lean_ctor_set(v___x_4553_, 1, v_k_4557_);
lean_ctor_set(v___x_4553_, 0, v___x_4568_);
v___x_4577_ = v___x_4553_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4568_);
lean_ctor_set(v_reuseFailAlloc_4578_, 1, v_k_4557_);
lean_ctor_set(v_reuseFailAlloc_4578_, 2, v_v_4558_);
lean_ctor_set(v_reuseFailAlloc_4578_, 3, v___y_4571_);
lean_ctor_set(v_reuseFailAlloc_4578_, 4, v___x_4575_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
v___jp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4583_ = lean_nat_add(v___x_4580_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec(v___x_4580_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v_l_4559_);
lean_ctor_set(v___x_4533_, 3, v_l_4542_);
lean_ctor_set(v___x_4533_, 2, v_v_4541_);
lean_ctor_set(v___x_4533_, 1, v_k_4540_);
lean_ctor_set(v___x_4533_, 0, v___x_4583_);
v___x_4585_ = v___x_4533_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_k_4540_);
lean_ctor_set(v_reuseFailAlloc_4589_, 2, v_v_4541_);
lean_ctor_set(v_reuseFailAlloc_4589_, 3, v_l_4542_);
lean_ctor_set(v_reuseFailAlloc_4589_, 4, v_l_4559_);
v___x_4585_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4586_; 
v___x_4586_ = lean_nat_add(v___x_4537_, v_size_4538_);
if (lean_obj_tag(v_r_4560_) == 0)
{
lean_object* v_size_4587_; 
v_size_4587_ = lean_ctor_get(v_r_4560_, 0);
lean_inc(v_size_4587_);
v___y_4570_ = v___x_4586_;
v___y_4571_ = v___x_4585_;
v___y_4572_ = v_size_4587_;
goto v___jp_4569_;
}
else
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___y_4570_ = v___x_4586_;
v___y_4571_ = v___x_4585_;
v___y_4572_ = v___x_4588_;
goto v___jp_4569_;
}
}
}
}
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
lean_del_object(v___x_4533_);
v___x_4598_ = lean_nat_add(v___x_4537_, v_size_4539_);
lean_dec(v_size_4539_);
v___x_4599_ = lean_nat_add(v___x_4598_, v_size_4538_);
lean_dec(v___x_4598_);
v___x_4600_ = lean_nat_add(v___x_4537_, v_size_4538_);
v___x_4601_ = lean_nat_add(v___x_4600_, v_size_4556_);
lean_dec(v___x_4600_);
lean_inc_ref(v_r_4531_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 4, v_r_4531_);
lean_ctor_set(v___x_4553_, 3, v_r_4543_);
lean_ctor_set(v___x_4553_, 2, v_v_4529_);
lean_ctor_set(v___x_4553_, 1, v_k_4528_);
lean_ctor_set(v___x_4553_, 0, v___x_4601_);
v___x_4603_ = v___x_4553_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4616_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4616_, 3, v_r_4543_);
lean_ctor_set(v_reuseFailAlloc_4616_, 4, v_r_4531_);
v___x_4603_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
v_isSharedCheck_4610_ = !lean_is_exclusive(v_r_4531_);
if (v_isSharedCheck_4610_ == 0)
{
lean_object* v_unused_4611_; lean_object* v_unused_4612_; lean_object* v_unused_4613_; lean_object* v_unused_4614_; lean_object* v_unused_4615_; 
v_unused_4611_ = lean_ctor_get(v_r_4531_, 4);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_r_4531_, 3);
lean_dec(v_unused_4612_);
v_unused_4613_ = lean_ctor_get(v_r_4531_, 2);
lean_dec(v_unused_4613_);
v_unused_4614_ = lean_ctor_get(v_r_4531_, 1);
lean_dec(v_unused_4614_);
v_unused_4615_ = lean_ctor_get(v_r_4531_, 0);
lean_dec(v_unused_4615_);
v___x_4605_ = v_r_4531_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_dec(v_r_4531_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 4, v___x_4603_);
lean_ctor_set(v___x_4605_, 3, v_l_4542_);
lean_ctor_set(v___x_4605_, 2, v_v_4541_);
lean_ctor_set(v___x_4605_, 1, v_k_4540_);
lean_ctor_set(v___x_4605_, 0, v___x_4599_);
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_k_4540_);
lean_ctor_set(v_reuseFailAlloc_4609_, 2, v_v_4541_);
lean_ctor_set(v_reuseFailAlloc_4609_, 3, v_l_4542_);
lean_ctor_set(v_reuseFailAlloc_4609_, 4, v___x_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4623_; 
v_l_4623_ = lean_ctor_get(v_impl_4536_, 3);
lean_inc(v_l_4623_);
if (lean_obj_tag(v_l_4623_) == 0)
{
lean_object* v_r_4624_; lean_object* v_k_4625_; lean_object* v_v_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4637_; 
v_r_4624_ = lean_ctor_get(v_impl_4536_, 4);
v_k_4625_ = lean_ctor_get(v_impl_4536_, 1);
v_v_4626_ = lean_ctor_get(v_impl_4536_, 2);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_impl_4536_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; lean_object* v_unused_4639_; 
v_unused_4638_ = lean_ctor_get(v_impl_4536_, 3);
lean_dec(v_unused_4638_);
v_unused_4639_ = lean_ctor_get(v_impl_4536_, 0);
lean_dec(v_unused_4639_);
v___x_4628_ = v_impl_4536_;
v_isShared_4629_ = v_isSharedCheck_4637_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_r_4624_);
lean_inc(v_v_4626_);
lean_inc(v_k_4625_);
lean_dec(v_impl_4536_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4637_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4630_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4624_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 3, v_r_4624_);
lean_ctor_set(v___x_4628_, 2, v_v_4529_);
lean_ctor_set(v___x_4628_, 1, v_k_4528_);
lean_ctor_set(v___x_4628_, 0, v___x_4537_);
v___x_4632_ = v___x_4628_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_r_4624_);
lean_ctor_set(v_reuseFailAlloc_4636_, 4, v_r_4624_);
v___x_4632_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4634_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v___x_4632_);
lean_ctor_set(v___x_4533_, 3, v_l_4623_);
lean_ctor_set(v___x_4533_, 2, v_v_4626_);
lean_ctor_set(v___x_4533_, 1, v_k_4625_);
lean_ctor_set(v___x_4533_, 0, v___x_4630_);
v___x_4634_ = v___x_4533_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_k_4625_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_v_4626_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_l_4623_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_object* v_r_4640_; 
v_r_4640_ = lean_ctor_get(v_impl_4536_, 4);
lean_inc(v_r_4640_);
if (lean_obj_tag(v_r_4640_) == 0)
{
lean_object* v_k_4641_; lean_object* v_v_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4665_; 
v_k_4641_ = lean_ctor_get(v_impl_4536_, 1);
v_v_4642_ = lean_ctor_get(v_impl_4536_, 2);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_impl_4536_);
if (v_isSharedCheck_4665_ == 0)
{
lean_object* v_unused_4666_; lean_object* v_unused_4667_; lean_object* v_unused_4668_; 
v_unused_4666_ = lean_ctor_get(v_impl_4536_, 4);
lean_dec(v_unused_4666_);
v_unused_4667_ = lean_ctor_get(v_impl_4536_, 3);
lean_dec(v_unused_4667_);
v_unused_4668_ = lean_ctor_get(v_impl_4536_, 0);
lean_dec(v_unused_4668_);
v___x_4644_ = v_impl_4536_;
v_isShared_4645_ = v_isSharedCheck_4665_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_v_4642_);
lean_inc(v_k_4641_);
lean_dec(v_impl_4536_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4665_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v_k_4646_; lean_object* v_v_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4661_; 
v_k_4646_ = lean_ctor_get(v_r_4640_, 1);
v_v_4647_ = lean_ctor_get(v_r_4640_, 2);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_r_4640_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; lean_object* v_unused_4663_; lean_object* v_unused_4664_; 
v_unused_4662_ = lean_ctor_get(v_r_4640_, 4);
lean_dec(v_unused_4662_);
v_unused_4663_ = lean_ctor_get(v_r_4640_, 3);
lean_dec(v_unused_4663_);
v_unused_4664_ = lean_ctor_get(v_r_4640_, 0);
lean_dec(v_unused_4664_);
v___x_4649_ = v_r_4640_;
v_isShared_4650_ = v_isSharedCheck_4661_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_v_4647_);
lean_inc(v_k_4646_);
lean_dec(v_r_4640_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4661_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4653_; 
v___x_4651_ = lean_unsigned_to_nat(3u);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 4, v_l_4623_);
lean_ctor_set(v___x_4649_, 3, v_l_4623_);
lean_ctor_set(v___x_4649_, 2, v_v_4642_);
lean_ctor_set(v___x_4649_, 1, v_k_4641_);
lean_ctor_set(v___x_4649_, 0, v___x_4537_);
v___x_4653_ = v___x_4649_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_k_4641_);
lean_ctor_set(v_reuseFailAlloc_4660_, 2, v_v_4642_);
lean_ctor_set(v_reuseFailAlloc_4660_, 3, v_l_4623_);
lean_ctor_set(v_reuseFailAlloc_4660_, 4, v_l_4623_);
v___x_4653_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4655_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 4, v_l_4623_);
lean_ctor_set(v___x_4644_, 2, v_v_4529_);
lean_ctor_set(v___x_4644_, 1, v_k_4528_);
lean_ctor_set(v___x_4644_, 0, v___x_4537_);
v___x_4655_ = v___x_4644_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4659_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4659_, 3, v_l_4623_);
lean_ctor_set(v_reuseFailAlloc_4659_, 4, v_l_4623_);
v___x_4655_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4657_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v___x_4655_);
lean_ctor_set(v___x_4533_, 3, v___x_4653_);
lean_ctor_set(v___x_4533_, 2, v_v_4647_);
lean_ctor_set(v___x_4533_, 1, v_k_4646_);
lean_ctor_set(v___x_4533_, 0, v___x_4651_);
v___x_4657_ = v___x_4533_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v_k_4646_);
lean_ctor_set(v_reuseFailAlloc_4658_, 2, v_v_4647_);
lean_ctor_set(v_reuseFailAlloc_4658_, 3, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4658_, 4, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
else
{
lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4669_ = lean_unsigned_to_nat(2u);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v_r_4640_);
lean_ctor_set(v___x_4533_, 3, v_impl_4536_);
lean_ctor_set(v___x_4533_, 0, v___x_4669_);
v___x_4671_ = v___x_4533_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
lean_ctor_set(v_reuseFailAlloc_4672_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4672_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4672_, 3, v_impl_4536_);
lean_ctor_set(v_reuseFailAlloc_4672_, 4, v_r_4640_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4674_; 
lean_dec(v_v_4529_);
lean_dec(v_k_4528_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 2, v_v_4525_);
lean_ctor_set(v___x_4533_, 1, v_k_4524_);
v___x_4674_ = v___x_4533_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_size_4527_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_k_4524_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_v_4525_);
lean_ctor_set(v_reuseFailAlloc_4675_, 3, v_l_4530_);
lean_ctor_set(v_reuseFailAlloc_4675_, 4, v_r_4531_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
default: 
{
lean_object* v_impl_4676_; lean_object* v___x_4677_; 
lean_dec(v_size_4527_);
v_impl_4676_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4524_, v_v_4525_, v_r_4531_);
v___x_4677_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4530_) == 0)
{
lean_object* v_size_4678_; lean_object* v_size_4679_; lean_object* v_k_4680_; lean_object* v_v_4681_; lean_object* v_l_4682_; lean_object* v_r_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; 
v_size_4678_ = lean_ctor_get(v_l_4530_, 0);
v_size_4679_ = lean_ctor_get(v_impl_4676_, 0);
lean_inc(v_size_4679_);
v_k_4680_ = lean_ctor_get(v_impl_4676_, 1);
lean_inc(v_k_4680_);
v_v_4681_ = lean_ctor_get(v_impl_4676_, 2);
lean_inc(v_v_4681_);
v_l_4682_ = lean_ctor_get(v_impl_4676_, 3);
lean_inc(v_l_4682_);
v_r_4683_ = lean_ctor_get(v_impl_4676_, 4);
lean_inc(v_r_4683_);
v___x_4684_ = lean_unsigned_to_nat(3u);
v___x_4685_ = lean_nat_mul(v___x_4684_, v_size_4678_);
v___x_4686_ = lean_nat_dec_lt(v___x_4685_, v_size_4679_);
lean_dec(v___x_4685_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; 
lean_dec(v_r_4683_);
lean_dec(v_l_4682_);
lean_dec(v_v_4681_);
lean_dec(v_k_4680_);
v___x_4687_ = lean_nat_add(v___x_4677_, v_size_4678_);
v___x_4688_ = lean_nat_add(v___x_4687_, v_size_4679_);
lean_dec(v_size_4679_);
lean_dec(v___x_4687_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v_impl_4676_);
lean_ctor_set(v___x_4533_, 0, v___x_4688_);
v___x_4690_ = v___x_4533_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4691_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4691_, 3, v_l_4530_);
lean_ctor_set(v_reuseFailAlloc_4691_, 4, v_impl_4676_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
else
{
lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4755_; 
v_isSharedCheck_4755_ = !lean_is_exclusive(v_impl_4676_);
if (v_isSharedCheck_4755_ == 0)
{
lean_object* v_unused_4756_; lean_object* v_unused_4757_; lean_object* v_unused_4758_; lean_object* v_unused_4759_; lean_object* v_unused_4760_; 
v_unused_4756_ = lean_ctor_get(v_impl_4676_, 4);
lean_dec(v_unused_4756_);
v_unused_4757_ = lean_ctor_get(v_impl_4676_, 3);
lean_dec(v_unused_4757_);
v_unused_4758_ = lean_ctor_get(v_impl_4676_, 2);
lean_dec(v_unused_4758_);
v_unused_4759_ = lean_ctor_get(v_impl_4676_, 1);
lean_dec(v_unused_4759_);
v_unused_4760_ = lean_ctor_get(v_impl_4676_, 0);
lean_dec(v_unused_4760_);
v___x_4693_ = v_impl_4676_;
v_isShared_4694_ = v_isSharedCheck_4755_;
goto v_resetjp_4692_;
}
else
{
lean_dec(v_impl_4676_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4755_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v_size_4695_; lean_object* v_k_4696_; lean_object* v_v_4697_; lean_object* v_l_4698_; lean_object* v_r_4699_; lean_object* v_size_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; uint8_t v___x_4703_; 
v_size_4695_ = lean_ctor_get(v_l_4682_, 0);
v_k_4696_ = lean_ctor_get(v_l_4682_, 1);
v_v_4697_ = lean_ctor_get(v_l_4682_, 2);
v_l_4698_ = lean_ctor_get(v_l_4682_, 3);
v_r_4699_ = lean_ctor_get(v_l_4682_, 4);
v_size_4700_ = lean_ctor_get(v_r_4683_, 0);
v___x_4701_ = lean_unsigned_to_nat(2u);
v___x_4702_ = lean_nat_mul(v___x_4701_, v_size_4700_);
v___x_4703_ = lean_nat_dec_lt(v_size_4695_, v___x_4702_);
lean_dec(v___x_4702_);
if (v___x_4703_ == 0)
{
lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4731_; 
lean_inc(v_r_4699_);
lean_inc(v_l_4698_);
lean_inc(v_v_4697_);
lean_inc(v_k_4696_);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_l_4682_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; 
v_unused_4732_ = lean_ctor_get(v_l_4682_, 4);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_l_4682_, 3);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_l_4682_, 2);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_l_4682_, 1);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_l_4682_, 0);
lean_dec(v_unused_4736_);
v___x_4705_ = v_l_4682_;
v_isShared_4706_ = v_isSharedCheck_4731_;
goto v_resetjp_4704_;
}
else
{
lean_dec(v_l_4682_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4731_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4721_; 
v___x_4707_ = lean_nat_add(v___x_4677_, v_size_4678_);
v___x_4708_ = lean_nat_add(v___x_4707_, v_size_4679_);
lean_dec(v_size_4679_);
if (lean_obj_tag(v_l_4698_) == 0)
{
lean_object* v_size_4729_; 
v_size_4729_ = lean_ctor_get(v_l_4698_, 0);
lean_inc(v_size_4729_);
v___y_4721_ = v_size_4729_;
goto v___jp_4720_;
}
else
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_unsigned_to_nat(0u);
v___y_4721_ = v___x_4730_;
goto v___jp_4720_;
}
v___jp_4709_:
{
lean_object* v___x_4713_; lean_object* v___x_4715_; 
v___x_4713_ = lean_nat_add(v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec(v___y_4711_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 4, v_r_4683_);
lean_ctor_set(v___x_4705_, 3, v_r_4699_);
lean_ctor_set(v___x_4705_, 2, v_v_4681_);
lean_ctor_set(v___x_4705_, 1, v_k_4680_);
lean_ctor_set(v___x_4705_, 0, v___x_4713_);
v___x_4715_ = v___x_4705_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_k_4680_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_v_4681_);
lean_ctor_set(v_reuseFailAlloc_4719_, 3, v_r_4699_);
lean_ctor_set(v_reuseFailAlloc_4719_, 4, v_r_4683_);
v___x_4715_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4717_; 
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 4, v___x_4715_);
lean_ctor_set(v___x_4693_, 3, v___y_4710_);
lean_ctor_set(v___x_4693_, 2, v_v_4697_);
lean_ctor_set(v___x_4693_, 1, v_k_4696_);
lean_ctor_set(v___x_4693_, 0, v___x_4708_);
v___x_4717_ = v___x_4693_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4708_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_k_4696_);
lean_ctor_set(v_reuseFailAlloc_4718_, 2, v_v_4697_);
lean_ctor_set(v_reuseFailAlloc_4718_, 3, v___y_4710_);
lean_ctor_set(v_reuseFailAlloc_4718_, 4, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
v___jp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4722_ = lean_nat_add(v___x_4707_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec(v___x_4707_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v_l_4698_);
lean_ctor_set(v___x_4533_, 0, v___x_4722_);
v___x_4724_ = v___x_4533_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_l_4530_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v_l_4698_);
v___x_4724_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; 
v___x_4725_ = lean_nat_add(v___x_4677_, v_size_4700_);
if (lean_obj_tag(v_r_4699_) == 0)
{
lean_object* v_size_4726_; 
v_size_4726_ = lean_ctor_get(v_r_4699_, 0);
lean_inc(v_size_4726_);
v___y_4710_ = v___x_4724_;
v___y_4711_ = v___x_4725_;
v___y_4712_ = v_size_4726_;
goto v___jp_4709_;
}
else
{
lean_object* v___x_4727_; 
v___x_4727_ = lean_unsigned_to_nat(0u);
v___y_4710_ = v___x_4724_;
v___y_4711_ = v___x_4725_;
v___y_4712_ = v___x_4727_;
goto v___jp_4709_;
}
}
}
}
}
else
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4741_; 
lean_del_object(v___x_4533_);
v___x_4737_ = lean_nat_add(v___x_4677_, v_size_4678_);
v___x_4738_ = lean_nat_add(v___x_4737_, v_size_4679_);
lean_dec(v_size_4679_);
v___x_4739_ = lean_nat_add(v___x_4737_, v_size_4695_);
lean_dec(v___x_4737_);
lean_inc_ref(v_l_4530_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 4, v_l_4682_);
lean_ctor_set(v___x_4693_, 3, v_l_4530_);
lean_ctor_set(v___x_4693_, 2, v_v_4529_);
lean_ctor_set(v___x_4693_, 1, v_k_4528_);
lean_ctor_set(v___x_4693_, 0, v___x_4739_);
v___x_4741_ = v___x_4693_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4739_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_l_4530_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v_l_4682_);
v___x_4741_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
v_isSharedCheck_4748_ = !lean_is_exclusive(v_l_4530_);
if (v_isSharedCheck_4748_ == 0)
{
lean_object* v_unused_4749_; lean_object* v_unused_4750_; lean_object* v_unused_4751_; lean_object* v_unused_4752_; lean_object* v_unused_4753_; 
v_unused_4749_ = lean_ctor_get(v_l_4530_, 4);
lean_dec(v_unused_4749_);
v_unused_4750_ = lean_ctor_get(v_l_4530_, 3);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_l_4530_, 2);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_l_4530_, 1);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_l_4530_, 0);
lean_dec(v_unused_4753_);
v___x_4743_ = v_l_4530_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_dec(v_l_4530_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 4, v_r_4683_);
lean_ctor_set(v___x_4743_, 3, v___x_4741_);
lean_ctor_set(v___x_4743_, 2, v_v_4681_);
lean_ctor_set(v___x_4743_, 1, v_k_4680_);
lean_ctor_set(v___x_4743_, 0, v___x_4738_);
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_k_4680_);
lean_ctor_set(v_reuseFailAlloc_4747_, 2, v_v_4681_);
lean_ctor_set(v_reuseFailAlloc_4747_, 3, v___x_4741_);
lean_ctor_set(v_reuseFailAlloc_4747_, 4, v_r_4683_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4761_; 
v_l_4761_ = lean_ctor_get(v_impl_4676_, 3);
lean_inc(v_l_4761_);
if (lean_obj_tag(v_l_4761_) == 0)
{
lean_object* v_r_4762_; lean_object* v_k_4763_; lean_object* v_v_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4787_; 
v_r_4762_ = lean_ctor_get(v_impl_4676_, 4);
v_k_4763_ = lean_ctor_get(v_impl_4676_, 1);
v_v_4764_ = lean_ctor_get(v_impl_4676_, 2);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_impl_4676_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; lean_object* v_unused_4789_; 
v_unused_4788_ = lean_ctor_get(v_impl_4676_, 3);
lean_dec(v_unused_4788_);
v_unused_4789_ = lean_ctor_get(v_impl_4676_, 0);
lean_dec(v_unused_4789_);
v___x_4766_ = v_impl_4676_;
v_isShared_4767_ = v_isSharedCheck_4787_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_r_4762_);
lean_inc(v_v_4764_);
lean_inc(v_k_4763_);
lean_dec(v_impl_4676_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4787_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v_k_4768_; lean_object* v_v_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4783_; 
v_k_4768_ = lean_ctor_get(v_l_4761_, 1);
v_v_4769_ = lean_ctor_get(v_l_4761_, 2);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_l_4761_);
if (v_isSharedCheck_4783_ == 0)
{
lean_object* v_unused_4784_; lean_object* v_unused_4785_; lean_object* v_unused_4786_; 
v_unused_4784_ = lean_ctor_get(v_l_4761_, 4);
lean_dec(v_unused_4784_);
v_unused_4785_ = lean_ctor_get(v_l_4761_, 3);
lean_dec(v_unused_4785_);
v_unused_4786_ = lean_ctor_get(v_l_4761_, 0);
lean_dec(v_unused_4786_);
v___x_4771_ = v_l_4761_;
v_isShared_4772_ = v_isSharedCheck_4783_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_v_4769_);
lean_inc(v_k_4768_);
lean_dec(v_l_4761_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4783_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4773_; lean_object* v___x_4775_; 
v___x_4773_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4762_, 2);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 4, v_r_4762_);
lean_ctor_set(v___x_4771_, 3, v_r_4762_);
lean_ctor_set(v___x_4771_, 2, v_v_4529_);
lean_ctor_set(v___x_4771_, 1, v_k_4528_);
lean_ctor_set(v___x_4771_, 0, v___x_4677_);
v___x_4775_ = v___x_4771_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4782_, 3, v_r_4762_);
lean_ctor_set(v_reuseFailAlloc_4782_, 4, v_r_4762_);
v___x_4775_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4777_; 
lean_inc(v_r_4762_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 3, v_r_4762_);
lean_ctor_set(v___x_4766_, 0, v___x_4677_);
v___x_4777_ = v___x_4766_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4781_, 1, v_k_4763_);
lean_ctor_set(v_reuseFailAlloc_4781_, 2, v_v_4764_);
lean_ctor_set(v_reuseFailAlloc_4781_, 3, v_r_4762_);
lean_ctor_set(v_reuseFailAlloc_4781_, 4, v_r_4762_);
v___x_4777_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
lean_object* v___x_4779_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v___x_4777_);
lean_ctor_set(v___x_4533_, 3, v___x_4775_);
lean_ctor_set(v___x_4533_, 2, v_v_4769_);
lean_ctor_set(v___x_4533_, 1, v_k_4768_);
lean_ctor_set(v___x_4533_, 0, v___x_4773_);
v___x_4779_ = v___x_4533_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4773_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_k_4768_);
lean_ctor_set(v_reuseFailAlloc_4780_, 2, v_v_4769_);
lean_ctor_set(v_reuseFailAlloc_4780_, 3, v___x_4775_);
lean_ctor_set(v_reuseFailAlloc_4780_, 4, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
}
else
{
lean_object* v_r_4790_; 
v_r_4790_ = lean_ctor_get(v_impl_4676_, 4);
lean_inc(v_r_4790_);
if (lean_obj_tag(v_r_4790_) == 0)
{
lean_object* v_k_4791_; lean_object* v_v_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4803_; 
v_k_4791_ = lean_ctor_get(v_impl_4676_, 1);
v_v_4792_ = lean_ctor_get(v_impl_4676_, 2);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_impl_4676_);
if (v_isSharedCheck_4803_ == 0)
{
lean_object* v_unused_4804_; lean_object* v_unused_4805_; lean_object* v_unused_4806_; 
v_unused_4804_ = lean_ctor_get(v_impl_4676_, 4);
lean_dec(v_unused_4804_);
v_unused_4805_ = lean_ctor_get(v_impl_4676_, 3);
lean_dec(v_unused_4805_);
v_unused_4806_ = lean_ctor_get(v_impl_4676_, 0);
lean_dec(v_unused_4806_);
v___x_4794_ = v_impl_4676_;
v_isShared_4795_ = v_isSharedCheck_4803_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_v_4792_);
lean_inc(v_k_4791_);
lean_dec(v_impl_4676_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4803_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4796_; lean_object* v___x_4798_; 
v___x_4796_ = lean_unsigned_to_nat(3u);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 4, v_l_4761_);
lean_ctor_set(v___x_4794_, 2, v_v_4529_);
lean_ctor_set(v___x_4794_, 1, v_k_4528_);
lean_ctor_set(v___x_4794_, 0, v___x_4677_);
v___x_4798_ = v___x_4794_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4802_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4802_, 3, v_l_4761_);
lean_ctor_set(v_reuseFailAlloc_4802_, 4, v_l_4761_);
v___x_4798_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
lean_object* v___x_4800_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v_r_4790_);
lean_ctor_set(v___x_4533_, 3, v___x_4798_);
lean_ctor_set(v___x_4533_, 2, v_v_4792_);
lean_ctor_set(v___x_4533_, 1, v_k_4791_);
lean_ctor_set(v___x_4533_, 0, v___x_4796_);
v___x_4800_ = v___x_4533_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4796_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_k_4791_);
lean_ctor_set(v_reuseFailAlloc_4801_, 2, v_v_4792_);
lean_ctor_set(v_reuseFailAlloc_4801_, 3, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4801_, 4, v_r_4790_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4809_; 
v___x_4807_ = lean_unsigned_to_nat(2u);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v_impl_4676_);
lean_ctor_set(v___x_4533_, 3, v_r_4790_);
lean_ctor_set(v___x_4533_, 0, v___x_4807_);
v___x_4809_ = v___x_4533_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_k_4528_);
lean_ctor_set(v_reuseFailAlloc_4810_, 2, v_v_4529_);
lean_ctor_set(v_reuseFailAlloc_4810_, 3, v_r_4790_);
lean_ctor_set(v_reuseFailAlloc_4810_, 4, v_impl_4676_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
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
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = lean_unsigned_to_nat(1u);
v___x_4813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
lean_ctor_set(v___x_4813_, 1, v_k_4524_);
lean_ctor_set(v___x_4813_, 2, v_v_4525_);
lean_ctor_set(v___x_4813_, 3, v_t_4526_);
lean_ctor_set(v___x_4813_, 4, v_t_4526_);
return v___x_4813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4814_, lean_object* v_k_4815_){
_start:
{
if (lean_obj_tag(v_t_4814_) == 0)
{
lean_object* v_k_4816_; lean_object* v_v_4817_; lean_object* v_l_4818_; lean_object* v_r_4819_; uint8_t v___x_4820_; 
v_k_4816_ = lean_ctor_get(v_t_4814_, 1);
v_v_4817_ = lean_ctor_get(v_t_4814_, 2);
v_l_4818_ = lean_ctor_get(v_t_4814_, 3);
v_r_4819_ = lean_ctor_get(v_t_4814_, 4);
v___x_4820_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4815_, v_k_4816_);
switch(v___x_4820_)
{
case 0:
{
v_t_4814_ = v_l_4818_;
goto _start;
}
case 1:
{
lean_object* v___x_4822_; 
lean_inc(v_v_4817_);
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v_v_4817_);
return v___x_4822_;
}
default: 
{
v_t_4814_ = v_r_4819_;
goto _start;
}
}
}
else
{
lean_object* v___x_4824_; 
v___x_4824_ = lean_box(0);
return v___x_4824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4825_, lean_object* v_k_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4825_, v_k_4826_);
lean_dec(v_k_4826_);
lean_dec(v_t_4825_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4828_, lean_object* v_k_4829_, lean_object* v_v_4830_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4828_, v_k_4829_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4832_ = lean_box(0);
v___x_4833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4833_, 0, v_v_4830_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4829_, v___x_4833_, v_map_4828_);
return v___x_4834_;
}
else
{
lean_object* v_val_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v_val_4835_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_val_4835_);
lean_dec_ref_known(v___x_4831_, 1);
v___x_4836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4836_, 0, v_v_4830_);
lean_ctor_set(v___x_4836_, 1, v_val_4835_);
v___x_4837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4829_, v___x_4836_, v_map_4828_);
return v___x_4837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4838_, lean_object* v_map_4839_, lean_object* v_k_4840_, lean_object* v_v_4841_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4839_, v_k_4840_, v_v_4841_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4843_, lean_object* v_t_4844_, lean_object* v_k_4845_){
_start:
{
lean_object* v___x_4846_; 
v___x_4846_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4844_, v_k_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4847_, lean_object* v_t_4848_, lean_object* v_k_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4847_, v_t_4848_, v_k_4849_);
lean_dec(v_k_4849_);
lean_dec(v_t_4848_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4851_, lean_object* v_k_4852_, lean_object* v_v_4853_, lean_object* v_t_4854_, lean_object* v_hl_4855_){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4852_, v_v_4853_, v_t_4854_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4857_){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_box(1);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4859_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = lean_box(1);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4861_, lean_object* v_a_4862_, lean_object* v_b_4863_, lean_object* v_c_4864_){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v_a_4862_);
lean_ctor_set(v___x_4865_, 1, v_b_4863_);
v___x_4866_ = lean_apply_2(v_f_4861_, v___x_4865_, v_c_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4867_, lean_object* v_____do__lift_4868_){
_start:
{
lean_object* v_a_4869_; lean_object* v___x_4870_; 
v_a_4869_ = lean_ctor_get(v_____do__lift_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref(v_____do__lift_4868_);
v___x_4870_ = lean_apply_2(v_toPure_4867_, lean_box(0), v_a_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4871_, lean_object* v_m_4872_, lean_object* v_init_4873_, lean_object* v_f_4874_){
_start:
{
lean_object* v_toApplicative_4875_; lean_object* v_toBind_4876_; lean_object* v_toPure_4877_; lean_object* v___f_4878_; lean_object* v___x_4879_; lean_object* v___f_4880_; lean_object* v___x_4881_; 
v_toApplicative_4875_ = lean_ctor_get(v_inst_4871_, 0);
v_toBind_4876_ = lean_ctor_get(v_inst_4871_, 1);
lean_inc(v_toBind_4876_);
v_toPure_4877_ = lean_ctor_get(v_toApplicative_4875_, 1);
lean_inc(v_toPure_4877_);
v___f_4878_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4878_, 0, v_f_4874_);
v___x_4879_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4871_, v___f_4878_, v_init_4873_, v_m_4872_);
v___f_4880_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4880_, 0, v_toPure_4877_);
v___x_4881_ = lean_apply_4(v_toBind_4876_, lean_box(0), lean_box(0), v___x_4879_, v___f_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4882_, lean_object* v_00_u03b1_4883_, lean_object* v_inst_4884_, lean_object* v_00_u03b2_4885_, lean_object* v_m_4886_, lean_object* v_init_4887_, lean_object* v_f_4888_){
_start:
{
lean_object* v_toApplicative_4889_; lean_object* v_toBind_4890_; lean_object* v_toPure_4891_; lean_object* v___f_4892_; lean_object* v___x_4893_; lean_object* v___f_4894_; lean_object* v___x_4895_; 
v_toApplicative_4889_ = lean_ctor_get(v_inst_4884_, 0);
v_toBind_4890_ = lean_ctor_get(v_inst_4884_, 1);
lean_inc(v_toBind_4890_);
v_toPure_4891_ = lean_ctor_get(v_toApplicative_4889_, 1);
lean_inc(v_toPure_4891_);
v___f_4892_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4892_, 0, v_f_4888_);
v___x_4893_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4884_, v___f_4892_, v_init_4887_, v_m_4886_);
v___f_4894_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4894_, 0, v_toPure_4891_);
v___x_4895_ = lean_apply_4(v_toBind_4890_, lean_box(0), lean_box(0), v___x_4893_, v___f_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4896_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4897_, 0, lean_box(0));
lean_closure_set(v___x_4897_, 1, lean_box(0));
lean_closure_set(v___x_4897_, 2, v_inst_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4898_, lean_object* v_00_u03b1_4899_, lean_object* v_inst_4900_){
_start:
{
lean_object* v___x_4901_; 
v___x_4901_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4901_, 0, lean_box(0));
lean_closure_set(v___x_4901_, 1, lean_box(0));
lean_closure_set(v___x_4901_, 2, v_inst_4900_);
return v___x_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t v_x_4906_){
_start:
{
switch(v_x_4906_)
{
case 0:
{
lean_object* v___x_4907_; 
v___x_4907_ = lean_unsigned_to_nat(0u);
return v___x_4907_;
}
case 1:
{
lean_object* v___x_4908_; 
v___x_4908_ = lean_unsigned_to_nat(1u);
return v___x_4908_;
}
default: 
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_unsigned_to_nat(2u);
return v___x_4909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object* v_x_4910_){
_start:
{
uint8_t v_x_boxed_4911_; lean_object* v_res_4912_; 
v_x_boxed_4911_ = lean_unbox(v_x_4910_);
v_res_4912_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_boxed_4911_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4913_){
_start:
{
lean_inc(v_k_4913_);
return v_k_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4914_);
lean_dec(v_k_4914_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4916_, lean_object* v_ctorIdx_4917_, uint8_t v_t_4918_, lean_object* v_h_4919_, lean_object* v_k_4920_){
_start:
{
lean_inc(v_k_4920_);
return v_k_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4921_, lean_object* v_ctorIdx_4922_, lean_object* v_t_4923_, lean_object* v_h_4924_, lean_object* v_k_4925_){
_start:
{
uint8_t v_t_boxed_4926_; lean_object* v_res_4927_; 
v_t_boxed_4926_ = lean_unbox(v_t_4923_);
v_res_4927_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4921_, v_ctorIdx_4922_, v_t_boxed_4926_, v_h_4924_, v_k_4925_);
lean_dec(v_k_4925_);
lean_dec(v_ctorIdx_4922_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4928_){
_start:
{
lean_inc(v_default_4928_);
return v_default_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4929_);
lean_dec(v_default_4929_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4931_, uint8_t v_t_4932_, lean_object* v_h_4933_, lean_object* v_default_4934_){
_start:
{
lean_inc(v_default_4934_);
return v_default_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4935_, lean_object* v_t_4936_, lean_object* v_h_4937_, lean_object* v_default_4938_){
_start:
{
uint8_t v_t_boxed_4939_; lean_object* v_res_4940_; 
v_t_boxed_4939_ = lean_unbox(v_t_4936_);
v_res_4940_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4935_, v_t_boxed_4939_, v_h_4937_, v_default_4938_);
lean_dec(v_default_4938_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4941_){
_start:
{
lean_inc(v_symbol_4941_);
return v_symbol_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4942_);
lean_dec(v_symbol_4942_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4944_, uint8_t v_t_4945_, lean_object* v_h_4946_, lean_object* v_symbol_4947_){
_start:
{
lean_inc(v_symbol_4947_);
return v_symbol_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4948_, lean_object* v_t_4949_, lean_object* v_h_4950_, lean_object* v_symbol_4951_){
_start:
{
uint8_t v_t_boxed_4952_; lean_object* v_res_4953_; 
v_t_boxed_4952_ = lean_unbox(v_t_4949_);
v_res_4953_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4948_, v_t_boxed_4952_, v_h_4950_, v_symbol_4951_);
lean_dec(v_symbol_4951_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4954_){
_start:
{
lean_inc(v_both_4954_);
return v_both_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4955_);
lean_dec(v_both_4955_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4957_, uint8_t v_t_4958_, lean_object* v_h_4959_, lean_object* v_both_4960_){
_start:
{
lean_inc(v_both_4960_);
return v_both_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4961_, lean_object* v_t_4962_, lean_object* v_h_4963_, lean_object* v_both_4964_){
_start:
{
uint8_t v_t_boxed_4965_; lean_object* v_res_4966_; 
v_t_boxed_4965_ = lean_unbox(v_t_4962_);
v_res_4966_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4961_, v_t_boxed_4965_, v_h_4963_, v_both_4964_);
lean_dec(v_both_4964_);
return v_res_4966_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4967_; 
v___x_4967_ = 0;
return v___x_4967_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4968_; 
v___x_4968_ = 0;
return v___x_4968_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4969_, uint8_t v_y_4970_){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; 
v___x_4971_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4969_);
v___x_4972_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_y_4970_);
v___x_4973_ = lean_nat_dec_eq(v___x_4971_, v___x_4972_);
lean_dec(v___x_4972_);
lean_dec(v___x_4971_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4974_, lean_object* v_y_4975_){
_start:
{
uint8_t v_x_17__boxed_4976_; uint8_t v_y_18__boxed_4977_; uint8_t v_res_4978_; lean_object* v_r_4979_; 
v_x_17__boxed_4976_ = lean_unbox(v_x_4974_);
v_y_18__boxed_4977_ = lean_unbox(v_y_4975_);
v_res_4978_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_17__boxed_4976_, v_y_18__boxed_4977_);
v_r_4979_ = lean_box(v_res_4978_);
return v_r_4979_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = lean_unsigned_to_nat(2u);
v___x_4992_ = lean_nat_to_int(v___x_4991_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4993_, lean_object* v_prec_4994_){
_start:
{
lean_object* v___y_4996_; lean_object* v___y_5003_; lean_object* v___y_5010_; 
switch(v_x_4993_)
{
case 0:
{
lean_object* v___x_5016_; uint8_t v___x_5017_; 
v___x_5016_ = lean_unsigned_to_nat(1024u);
v___x_5017_ = lean_nat_dec_le(v___x_5016_, v_prec_4994_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; 
v___x_5018_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4996_ = v___x_5018_;
goto v___jp_4995_;
}
else
{
lean_object* v___x_5019_; 
v___x_5019_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4996_ = v___x_5019_;
goto v___jp_4995_;
}
}
case 1:
{
lean_object* v___x_5020_; uint8_t v___x_5021_; 
v___x_5020_ = lean_unsigned_to_nat(1024u);
v___x_5021_ = lean_nat_dec_le(v___x_5020_, v_prec_4994_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
v___x_5022_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_5003_ = v___x_5022_;
goto v___jp_5002_;
}
else
{
lean_object* v___x_5023_; 
v___x_5023_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_5003_ = v___x_5023_;
goto v___jp_5002_;
}
}
default: 
{
lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5024_ = lean_unsigned_to_nat(1024u);
v___x_5025_ = lean_nat_dec_le(v___x_5024_, v_prec_4994_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
v___x_5026_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_5010_ = v___x_5026_;
goto v___jp_5009_;
}
else
{
lean_object* v___x_5027_; 
v___x_5027_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_5010_ = v___x_5027_;
goto v___jp_5009_;
}
}
}
v___jp_4995_:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_4997_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_4996_);
v___x_4998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___y_4996_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
v___x_4999_ = 0;
v___x_5000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5000_, 0, v___x_4998_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*1, v___x_4999_);
v___x_5001_ = l_Repr_addAppParen(v___x_5000_, v_prec_4994_);
return v___x_5001_;
}
v___jp_5002_:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5004_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_5003_);
v___x_5005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___y_5003_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = 0;
v___x_5007_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5007_, 0, v___x_5005_);
lean_ctor_set_uint8(v___x_5007_, sizeof(void*)*1, v___x_5006_);
v___x_5008_ = l_Repr_addAppParen(v___x_5007_, v_prec_4994_);
return v___x_5008_;
}
v___jp_5009_:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5011_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_5010_);
v___x_5012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___y_5010_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = 0;
v___x_5014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5014_, 0, v___x_5012_);
lean_ctor_set_uint8(v___x_5014_, sizeof(void*)*1, v___x_5013_);
v___x_5015_ = l_Repr_addAppParen(v___x_5014_, v_prec_4994_);
return v___x_5015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_5028_, lean_object* v_prec_5029_){
_start:
{
uint8_t v_x_175__boxed_5030_; lean_object* v_res_5031_; 
v_x_175__boxed_5030_ = lean_unbox(v_x_5028_);
v_res_5031_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_175__boxed_5030_, v_prec_5029_);
lean_dec(v_prec_5029_);
return v_res_5031_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5034_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5037_ = 0;
v___x_5038_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_5039_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_5040_ = lean_box(0);
v___x_5041_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5041_, 0, v___x_5040_);
lean_ctor_set(v___x_5041_, 1, v___x_5039_);
lean_ctor_set(v___x_5041_, 2, v___x_5038_);
lean_ctor_set_uint8(v___x_5041_, sizeof(void*)*3, v___x_5037_);
return v___x_5041_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_5042_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_5044_, lean_object* v_c_5045_, lean_object* v_s_5046_, uint8_t v_behavior_5047_){
_start:
{
lean_object* v___x_5048_; lean_object* v_fst_5049_; lean_object* v_snd_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5092_; 
v___x_5048_ = l_Lean_Parser_peekToken(v_c_5045_, v_s_5046_);
v_fst_5049_ = lean_ctor_get(v___x_5048_, 0);
v_snd_5050_ = lean_ctor_get(v___x_5048_, 1);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5052_ = v___x_5048_;
v_isShared_5053_ = v_isSharedCheck_5092_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_snd_5050_);
lean_inc(v_fst_5049_);
lean_dec(v___x_5048_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5092_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v_n_5055_; 
if (lean_obj_tag(v_snd_5050_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
lean_del_object(v___x_5052_);
lean_dec(v_fst_5049_);
v_a_5067_ = lean_ctor_get(v_snd_5050_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v_snd_5050_, 1);
v___x_5068_ = lean_box(0);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v_a_5067_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
return v___x_5069_;
}
else
{
lean_object* v_a_5070_; 
v_a_5070_ = lean_ctor_get(v_snd_5050_, 0);
lean_inc(v_a_5070_);
lean_dec_ref_known(v_snd_5050_, 1);
switch(lean_obj_tag(v_a_5070_))
{
case 2:
{
lean_object* v_val_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v_val_5071_ = lean_ctor_get(v_a_5070_, 1);
lean_inc_ref(v_val_5071_);
lean_dec_ref_known(v_a_5070_, 2);
v___x_5072_ = lean_box(0);
v___x_5073_ = l_Lean_Name_str___override(v___x_5072_, v_val_5071_);
v_n_5055_ = v___x_5073_;
goto v___jp_5054_;
}
case 3:
{
switch(v_behavior_5047_)
{
case 0:
{
lean_dec_ref_known(v_a_5070_, 4);
goto v___jp_5065_;
}
case 1:
{
lean_object* v_val_5074_; lean_object* v___x_5075_; 
v_val_5074_ = lean_ctor_get(v_a_5070_, 2);
lean_inc(v_val_5074_);
lean_dec_ref_known(v_a_5070_, 4);
v___x_5075_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5044_, v_val_5074_);
lean_dec(v_val_5074_);
if (lean_obj_tag(v___x_5075_) == 0)
{
goto v___jp_5065_;
}
else
{
lean_object* v_val_5076_; lean_object* v___x_5077_; 
lean_del_object(v___x_5052_);
v_val_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_val_5076_);
lean_dec_ref_known(v___x_5075_, 1);
v___x_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5077_, 0, v_fst_5049_);
lean_ctor_set(v___x_5077_, 1, v_val_5076_);
return v___x_5077_;
}
}
default: 
{
lean_object* v_val_5078_; lean_object* v___x_5079_; 
v_val_5078_ = lean_ctor_get(v_a_5070_, 2);
lean_inc(v_val_5078_);
lean_dec_ref_known(v_a_5070_, 4);
v___x_5079_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5044_, v_val_5078_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_dec(v_val_5078_);
goto v___jp_5065_;
}
else
{
lean_object* v_val_5080_; lean_object* v___x_5081_; uint8_t v___x_5082_; 
lean_del_object(v___x_5052_);
v_val_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_val_5080_);
lean_dec_ref_known(v___x_5079_, 1);
v___x_5081_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_5082_ = lean_name_eq(v_val_5078_, v___x_5081_);
lean_dec(v_val_5078_);
if (v___x_5082_ == 0)
{
lean_object* v___x_5083_; 
v___x_5083_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5044_, v___x_5081_);
if (lean_obj_tag(v___x_5083_) == 1)
{
lean_object* v_val_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v_val_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_val_5084_);
lean_dec_ref_known(v___x_5083_, 1);
v___x_5085_ = l_List_appendTR___redArg(v_val_5080_, v_val_5084_);
v___x_5086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5086_, 0, v_fst_5049_);
lean_ctor_set(v___x_5086_, 1, v___x_5085_);
return v___x_5086_;
}
else
{
lean_object* v___x_5087_; 
lean_dec(v___x_5083_);
v___x_5087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5087_, 0, v_fst_5049_);
lean_ctor_set(v___x_5087_, 1, v_val_5080_);
return v___x_5087_;
}
}
else
{
lean_object* v___x_5088_; 
v___x_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5088_, 0, v_fst_5049_);
lean_ctor_set(v___x_5088_, 1, v_val_5080_);
return v___x_5088_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_5089_; 
v_kind_5089_ = lean_ctor_get(v_a_5070_, 1);
lean_inc(v_kind_5089_);
lean_dec_ref_known(v_a_5070_, 3);
v_n_5055_ = v_kind_5089_;
goto v___jp_5054_;
}
default: 
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
lean_dec(v_a_5070_);
lean_del_object(v___x_5052_);
v___x_5090_ = lean_box(0);
v___x_5091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5091_, 0, v_fst_5049_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
return v___x_5091_;
}
}
}
v___jp_5054_:
{
lean_object* v___x_5056_; 
v___x_5056_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5044_, v_n_5055_);
lean_dec(v_n_5055_);
if (lean_obj_tag(v___x_5056_) == 1)
{
lean_object* v_val_5057_; lean_object* v___x_5059_; 
v_val_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_val_5057_);
lean_dec_ref_known(v___x_5056_, 1);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v_val_5057_);
v___x_5059_ = v___x_5052_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_fst_5049_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_val_5057_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5063_; 
lean_dec(v___x_5056_);
v___x_5061_ = lean_box(0);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v___x_5061_);
v___x_5063_ = v___x_5052_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_fst_5049_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5061_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
v___jp_5065_:
{
lean_object* v___x_5066_; 
v___x_5066_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_5055_ = v___x_5066_;
goto v___jp_5054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_5093_, lean_object* v_c_5094_, lean_object* v_s_5095_, lean_object* v_behavior_5096_){
_start:
{
uint8_t v_behavior_boxed_5097_; lean_object* v_res_5098_; 
v_behavior_boxed_5097_ = lean_unbox(v_behavior_5096_);
v_res_5098_ = l_Lean_Parser_indexed___redArg(v_map_5093_, v_c_5094_, v_s_5095_, v_behavior_boxed_5097_);
lean_dec(v_map_5093_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_5099_, lean_object* v_map_5100_, lean_object* v_c_5101_, lean_object* v_s_5102_, uint8_t v_behavior_5103_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Parser_indexed___redArg(v_map_5100_, v_c_5101_, v_s_5102_, v_behavior_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_5105_, lean_object* v_map_5106_, lean_object* v_c_5107_, lean_object* v_s_5108_, lean_object* v_behavior_5109_){
_start:
{
uint8_t v_behavior_boxed_5110_; lean_object* v_res_5111_; 
v_behavior_boxed_5110_ = lean_unbox(v_behavior_5109_);
v_res_5111_ = l_Lean_Parser_indexed(v_00_u03b1_5105_, v_map_5106_, v_c_5107_, v_s_5108_, v_behavior_boxed_5110_);
lean_dec(v_map_5106_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Lean_Parser_whitespace(v___y_5113_, v___y_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_5116_, v___y_5117_, v___y_5118_);
lean_dec(v_x_5116_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___f_5122_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_5123_ = lean_st_mk_ref(v___f_5122_);
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v___x_5123_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_5127_){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = lean_st_ref_get(v___x_5127_);
v___x_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5129_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_5131_);
lean_dec(v___x_5131_);
return v_res_5133_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5134_; lean_object* v___f_5135_; 
v___x_5134_ = l_Lean_Parser_categoryParserFnRef;
v___f_5135_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5135_, 0, v___x_5134_);
return v___f_5135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___f_5137_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_5138_ = lean_box(0);
v___x_5139_ = lean_box(2);
v___x_5140_ = l_Lean_registerEnvExtension___redArg(v___f_5137_, v___x_5138_, v___x_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
lean_object* v___x_5146_; 
v___x_5146_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_5144_, v___y_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_5147_, v___y_5148_, v___y_5149_);
lean_dec_ref(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_dec(v_a_5147_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_5154_, lean_object* v_ctx_5155_, lean_object* v_s_5156_){
_start:
{
lean_object* v_toParserModuleContext_5157_; lean_object* v_env_5158_; lean_object* v___x_5159_; lean_object* v_asyncMode_5160_; lean_object* v___f_5161_; lean_object* v___x_5162_; lean_object* v___x_11__overap_5163_; lean_object* v___x_5164_; 
v_toParserModuleContext_5157_ = lean_ctor_get(v_ctx_5155_, 1);
v_env_5158_ = lean_ctor_get(v_toParserModuleContext_5157_, 0);
v___x_5159_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_5160_ = lean_ctor_get(v___x_5159_, 2);
v___f_5161_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_5162_ = lean_box(0);
lean_inc_ref(v_env_5158_);
v___x_11__overap_5163_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_5161_, v___x_5159_, v_env_5158_, v_asyncMode_5160_, v___x_5162_);
v___x_5164_ = lean_apply_3(v___x_11__overap_5163_, v_catName_5154_, v_ctx_5155_, v_s_5156_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_5165_, lean_object* v_x_5166_){
_start:
{
lean_object* v_quotDepth_5167_; uint8_t v_suppressInsideQuot_5168_; lean_object* v_savedPos_x3f_5169_; lean_object* v_forbiddenTks_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
v_quotDepth_5167_ = lean_ctor_get(v_x_5166_, 1);
v_suppressInsideQuot_5168_ = lean_ctor_get_uint8(v_x_5166_, sizeof(void*)*4);
v_savedPos_x3f_5169_ = lean_ctor_get(v_x_5166_, 2);
v_forbiddenTks_5170_ = lean_ctor_get(v_x_5166_, 3);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_x_5166_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v_x_5166_, 0);
lean_dec(v_unused_5178_);
v___x_5172_ = v_x_5166_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_forbiddenTks_5170_);
lean_inc(v_savedPos_x3f_5169_);
lean_inc(v_quotDepth_5167_);
lean_dec(v_x_5166_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
lean_ctor_set(v___x_5172_, 0, v_prec_5165_);
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_prec_5165_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_quotDepth_5167_);
lean_ctor_set(v_reuseFailAlloc_5176_, 2, v_savedPos_x3f_5169_);
lean_ctor_set(v_reuseFailAlloc_5176_, 3, v_forbiddenTks_5170_);
lean_ctor_set_uint8(v_reuseFailAlloc_5176_, sizeof(void*)*4, v_suppressInsideQuot_5168_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_5179_, lean_object* v_prec_5180_){
_start:
{
lean_object* v___f_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___f_5181_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_5181_, 0, v_prec_5180_);
v___x_5182_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_5179_);
v___x_5183_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_5183_, 0, v_catName_5179_);
v___x_5184_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_5184_, 0, v_catName_5179_);
lean_closure_set(v___x_5184_, 1, v___x_5183_);
v___x_5185_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5185_, 0, v___f_5181_);
lean_closure_set(v___x_5185_, 1, v___x_5184_);
v___x_5186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5182_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5190_){
_start:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5191_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5192_ = l_Lean_Parser_categoryParser(v___x_5191_, v_prec_5190_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5194_, lean_object* v_s_5195_){
_start:
{
lean_object* v_stxStack_5196_; lean_object* v_pos_5197_; lean_object* v_prev_5198_; uint8_t v___x_5199_; 
v_stxStack_5196_ = lean_ctor_get(v_s_5195_, 0);
v_pos_5197_ = lean_ctor_get(v_s_5195_, 2);
v_prev_5198_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5196_);
v___x_5199_ = l_Lean_Parser_checkTailNoWs(v_prev_5198_);
lean_dec(v_prev_5198_);
if (v___x_5199_ == 0)
{
return v_s_5195_;
}
else
{
lean_object* v_toInputContext_5200_; uint8_t v___x_5201_; 
v_toInputContext_5200_ = lean_ctor_get(v_c_5194_, 0);
v___x_5201_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5200_, v_pos_5197_);
if (v___x_5201_ == 0)
{
lean_object* v_inputString_5202_; uint32_t v_curr_5203_; uint32_t v___x_5204_; uint8_t v___x_5205_; 
v_inputString_5202_ = lean_ctor_get(v_toInputContext_5200_, 0);
v_curr_5203_ = lean_string_utf8_get_fast(v_inputString_5202_, v_pos_5197_);
v___x_5204_ = 58;
v___x_5205_ = lean_uint32_dec_eq(v_curr_5203_, v___x_5204_);
if (v___x_5205_ == 0)
{
return v_s_5195_;
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5206_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5207_ = lean_box(0);
v___x_5208_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5195_, v___x_5206_, v___x_5207_, v___x_5205_);
return v___x_5208_;
}
}
else
{
return v_s_5195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5209_, lean_object* v_s_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5209_, v_s_5210_);
lean_dec_ref(v_c_5209_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5224_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5225_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5226_ = l_Lean_addBuiltinDocString(v___x_5224_, v___x_5225_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5229_, lean_object* v_p_5230_, lean_object* v_c_5231_, lean_object* v_s_5232_){
_start:
{
lean_object* v___x_5233_; lean_object* v_errorMsg_5234_; 
v___x_5233_ = lean_apply_2(v_p_5230_, v_c_5231_, v_s_5232_);
v_errorMsg_5234_ = lean_ctor_get(v___x_5233_, 4);
lean_inc(v_errorMsg_5234_);
if (lean_obj_tag(v_errorMsg_5234_) == 1)
{
lean_object* v_val_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5265_; 
v_val_5235_ = lean_ctor_get(v_errorMsg_5234_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v_errorMsg_5234_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5237_ = v_errorMsg_5234_;
v_isShared_5238_ = v_isSharedCheck_5265_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_val_5235_);
lean_dec(v_errorMsg_5234_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5265_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v_stxStack_5239_; lean_object* v_lhsPrec_5240_; lean_object* v_pos_5241_; lean_object* v_cache_5242_; lean_object* v_recoveredErrors_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5263_; 
v_stxStack_5239_ = lean_ctor_get(v___x_5233_, 0);
v_lhsPrec_5240_ = lean_ctor_get(v___x_5233_, 1);
v_pos_5241_ = lean_ctor_get(v___x_5233_, 2);
v_cache_5242_ = lean_ctor_get(v___x_5233_, 3);
v_recoveredErrors_5243_ = lean_ctor_get(v___x_5233_, 5);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5263_ == 0)
{
lean_object* v_unused_5264_; 
v_unused_5264_ = lean_ctor_get(v___x_5233_, 4);
lean_dec(v_unused_5264_);
v___x_5245_ = v___x_5233_;
v_isShared_5246_ = v_isSharedCheck_5263_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_recoveredErrors_5243_);
lean_inc(v_cache_5242_);
lean_inc(v_pos_5241_);
lean_inc(v_lhsPrec_5240_);
lean_inc(v_stxStack_5239_);
lean_dec(v___x_5233_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5263_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v_unexpectedTk_5247_; lean_object* v_unexpected_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5261_; 
v_unexpectedTk_5247_ = lean_ctor_get(v_val_5235_, 0);
v_unexpected_5248_ = lean_ctor_get(v_val_5235_, 1);
v_isSharedCheck_5261_ = !lean_is_exclusive(v_val_5235_);
if (v_isSharedCheck_5261_ == 0)
{
lean_object* v_unused_5262_; 
v_unused_5262_ = lean_ctor_get(v_val_5235_, 2);
lean_dec(v_unused_5262_);
v___x_5250_ = v_val_5235_;
v_isShared_5251_ = v_isSharedCheck_5261_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_unexpected_5248_);
lean_inc(v_unexpectedTk_5247_);
lean_dec(v_val_5235_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5261_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
lean_ctor_set(v___x_5250_, 2, v_expected_5229_);
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_unexpectedTk_5247_);
lean_ctor_set(v_reuseFailAlloc_5260_, 1, v_unexpected_5248_);
lean_ctor_set(v_reuseFailAlloc_5260_, 2, v_expected_5229_);
v___x_5253_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
lean_object* v___x_5255_; 
if (v_isShared_5238_ == 0)
{
lean_ctor_set(v___x_5237_, 0, v___x_5253_);
v___x_5255_ = v___x_5237_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5253_);
v___x_5255_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
lean_object* v___x_5257_; 
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 4, v___x_5255_);
v___x_5257_ = v___x_5245_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_stxStack_5239_);
lean_ctor_set(v_reuseFailAlloc_5258_, 1, v_lhsPrec_5240_);
lean_ctor_set(v_reuseFailAlloc_5258_, 2, v_pos_5241_);
lean_ctor_set(v_reuseFailAlloc_5258_, 3, v_cache_5242_);
lean_ctor_set(v_reuseFailAlloc_5258_, 4, v___x_5255_);
lean_ctor_set(v_reuseFailAlloc_5258_, 5, v_recoveredErrors_5243_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5234_);
lean_dec(v_expected_5229_);
return v___x_5233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5266_, lean_object* v_p_5267_){
_start:
{
lean_object* v_info_5268_; lean_object* v_fn_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5277_; 
v_info_5268_ = lean_ctor_get(v_p_5267_, 0);
v_fn_5269_ = lean_ctor_get(v_p_5267_, 1);
v_isSharedCheck_5277_ = !lean_is_exclusive(v_p_5267_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5271_ = v_p_5267_;
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_fn_5269_);
lean_inc(v_info_5268_);
lean_dec(v_p_5267_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5275_; 
v___x_5273_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5273_, 0, v_expected_5266_);
lean_closure_set(v___x_5273_, 1, v_fn_5269_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 1, v___x_5273_);
v___x_5275_ = v___x_5271_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_info_5268_);
lean_ctor_set(v_reuseFailAlloc_5276_, 1, v___x_5273_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5278_, lean_object* v_s_5279_){
_start:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5280_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_5281_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5279_, v___x_5280_);
return v___x_5281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5282_, lean_object* v_s_5283_){
_start:
{
lean_object* v_res_5284_; 
v_res_5284_ = l_Lean_Parser_pushNone___lam__0(v_x_5282_, v_s_5283_);
lean_dec_ref(v_x_5282_);
return v_res_5284_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5295_ = l_Lean_Parser_symbolNoAntiquot(v___x_5294_);
return v___x_5295_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5296_; lean_object* v___x_5297_; 
v___x_5296_ = lean_unsigned_to_nat(0u);
v___x_5297_ = l_Lean_Parser_termParser(v___x_5296_);
return v___x_5297_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5298_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5299_ = l_Lean_Parser_decQuotDepth(v___x_5298_);
return v___x_5299_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5301_ = l_Lean_Parser_symbolNoAntiquot(v___x_5300_);
return v___x_5301_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5302_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5303_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5304_ = l_Lean_Parser_andthen(v___x_5303_, v___x_5302_);
return v___x_5304_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5305_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5306_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5307_ = l_Lean_Parser_andthen(v___x_5306_, v___x_5305_);
return v___x_5307_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5308_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5309_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5310_ = l_Lean_Parser_node(v___x_5309_, v___x_5308_);
return v___x_5310_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5311_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5313_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5314_ = l_Lean_Parser_symbolNoAntiquot(v___x_5313_);
return v___x_5314_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5315_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5316_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5317_ = l_Lean_Parser_orelse(v___x_5316_, v___x_5315_);
return v___x_5317_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v___x_5318_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5319_ = l_Lean_Parser_identNoAntiquot;
v___x_5320_ = l_Lean_Parser_orelse(v___x_5319_, v___x_5318_);
return v___x_5320_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5321_; 
v___x_5321_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5321_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5323_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5324_ = l_Lean_Parser_checkNoWsBefore(v___x_5323_);
return v___x_5324_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5326_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5327_ = l_Lean_Parser_symbolNoAntiquot(v___x_5326_);
return v___x_5327_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5329_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5330_ = l_Lean_Parser_symbolNoAntiquot(v___x_5329_);
return v___x_5330_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5331_ = l_Lean_Parser_antiquotExpr;
v___x_5332_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5333_ = l_Lean_Parser_andthen(v___x_5332_, v___x_5331_);
return v___x_5333_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5334_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5335_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5336_ = l_Lean_Parser_andthen(v___x_5335_, v___x_5334_);
return v___x_5336_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5337_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5338_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5339_ = l_Lean_Parser_andthen(v___x_5338_, v___x_5337_);
return v___x_5339_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5340_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5341_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5342_ = l_Lean_Parser_andthen(v___x_5341_, v___x_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5346_, lean_object* v_s_5347_){
_start:
{
lean_object* v_pos_5348_; lean_object* v_errorMsg_5349_; lean_object* v___x_5350_; uint8_t v___x_5351_; 
v_pos_5348_ = lean_ctor_get(v_s_5347_, 2);
v_errorMsg_5349_ = lean_ctor_get(v_s_5347_, 4);
v___x_5350_ = lean_box(0);
v___x_5351_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5349_, v___x_5350_);
if (v___x_5351_ == 0)
{
lean_dec_ref(v_c_5346_);
return v_s_5347_;
}
else
{
lean_object* v___x_5352_; lean_object* v_fn_5353_; lean_object* v_iniSz_5354_; lean_object* v_s_5355_; lean_object* v_errorMsg_5356_; uint8_t v___x_5357_; 
lean_inc(v_pos_5348_);
v___x_5352_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5353_ = lean_ctor_get(v___x_5352_, 1);
v_iniSz_5354_ = l_Lean_Parser_ParserState_stackSize(v_s_5347_);
lean_inc_ref(v_fn_5353_);
v_s_5355_ = lean_apply_2(v_fn_5353_, v_c_5346_, v_s_5347_);
v_errorMsg_5356_ = lean_ctor_get(v_s_5355_, 4);
lean_inc(v_errorMsg_5356_);
v___x_5357_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5356_, v___x_5350_);
lean_dec(v_errorMsg_5356_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; 
v___x_5358_ = l_Lean_Parser_ParserState_restore(v_s_5355_, v_iniSz_5354_, v_pos_5348_);
lean_dec(v_iniSz_5354_);
return v___x_5358_;
}
else
{
lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
lean_dec(v_pos_5348_);
v___x_5359_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5360_ = lean_unsigned_to_nat(1u);
v___x_5361_ = lean_nat_sub(v_iniSz_5354_, v___x_5360_);
lean_dec(v_iniSz_5354_);
v___x_5362_ = l_Lean_Parser_ParserState_mkNode(v_s_5355_, v___x_5359_, v___x_5361_);
lean_dec(v___x_5361_);
return v___x_5362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_toInputContext_5366_; lean_object* v_s_5367_; lean_object* v_pos_5368_; lean_object* v_inputString_5369_; uint32_t v___x_5370_; uint32_t v___x_5371_; uint8_t v___x_5372_; 
v_toInputContext_5366_ = lean_ctor_get(v___y_5364_, 0);
lean_inc_ref(v___y_5364_);
v_s_5367_ = lean_apply_2(v_fn_5363_, v___y_5364_, v___y_5365_);
v_pos_5368_ = lean_ctor_get(v_s_5367_, 2);
lean_inc(v_pos_5368_);
v_inputString_5369_ = lean_ctor_get(v_toInputContext_5366_, 0);
v___x_5370_ = lean_string_utf8_get(v_inputString_5369_, v_pos_5368_);
lean_dec(v_pos_5368_);
v___x_5371_ = 37;
v___x_5372_ = lean_uint32_dec_eq(v___x_5370_, v___x_5371_);
if (v___x_5372_ == 0)
{
lean_dec_ref(v___y_5364_);
return v_s_5367_;
}
else
{
lean_object* v___x_5373_; 
v___x_5373_ = l_Lean_Parser_tokenAntiquotFn(v___y_5364_, v_s_5367_);
return v___x_5373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5374_){
_start:
{
lean_object* v_info_5375_; lean_object* v_fn_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5384_; 
v_info_5375_ = lean_ctor_get(v_p_5374_, 0);
v_fn_5376_ = lean_ctor_get(v_p_5374_, 1);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_p_5374_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5378_ = v_p_5374_;
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_fn_5376_);
lean_inc(v_info_5375_);
lean_dec(v_p_5374_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___f_5380_; lean_object* v___x_5382_; 
v___f_5380_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5380_, 0, v_fn_5376_);
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 1, v___f_5380_);
v___x_5382_ = v___x_5378_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_info_5375_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v___f_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5385_){
_start:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5386_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5385_);
v___x_5387_ = l_Lean_Parser_tokenWithAntiquot(v___x_5386_);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5390_, uint8_t v_includeIdent_5391_){
_start:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5390_, v_includeIdent_5391_);
v___x_5393_ = l_Lean_Parser_tokenWithAntiquot(v___x_5392_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5394_, lean_object* v_includeIdent_5395_){
_start:
{
uint8_t v_includeIdent_boxed_5396_; lean_object* v_res_5397_; 
v_includeIdent_boxed_5396_ = lean_unbox(v_includeIdent_5395_);
v_res_5397_ = l_Lean_Parser_nonReservedSymbol(v_sym_5394_, v_includeIdent_boxed_5396_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5398_, lean_object* v_asciiSym_5399_){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5400_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5398_, v_asciiSym_5399_);
v___x_5401_ = l_Lean_Parser_tokenWithAntiquot(v___x_5400_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5402_, lean_object* v_asciiSym_5403_, uint8_t v_preserveForPP_5404_){
_start:
{
lean_object* v___x_5405_; 
v___x_5405_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5402_, v_asciiSym_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5406_, lean_object* v_asciiSym_5407_, lean_object* v_preserveForPP_5408_){
_start:
{
uint8_t v_preserveForPP_boxed_5409_; lean_object* v_res_5410_; 
v_preserveForPP_boxed_5409_ = lean_unbox(v_preserveForPP_5408_);
v_res_5410_ = l_Lean_Parser_unicodeSymbol(v_sym_5406_, v_asciiSym_5407_, v_preserveForPP_boxed_5409_);
return v_res_5410_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5412_ = l_Lean_Parser_symbol(v___x_5411_);
return v___x_5412_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5413_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5414_ = lean_box(0);
v___x_5415_ = l_Lean_Parser_setExpected(v___x_5414_, v___x_5413_);
return v___x_5415_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5417_ = l_Lean_Parser_checkNoWsBefore(v___x_5416_);
return v___x_5417_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5418_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5419_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5420_ = l_Lean_Parser_andthen(v___x_5419_, v___x_5418_);
return v___x_5420_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; 
v___x_5421_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5422_ = l_Lean_Parser_manyNoAntiquot(v___x_5421_);
return v___x_5422_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5425_ = l_Lean_Parser_checkNoWsBefore(v___x_5424_);
return v___x_5425_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5434_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5435_ = l_Lean_Parser_symbol(v___x_5434_);
return v___x_5435_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5436_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5437_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5438_ = l_Lean_Parser_andthen(v___x_5437_, v___x_5436_);
return v___x_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5442_, lean_object* v_kind_5443_, uint8_t v_anonymous_5444_, uint8_t v_isPseudoKind_5445_){
_start:
{
lean_object* v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5461_; 
if (v_isPseudoKind_5445_ == 0)
{
lean_object* v___x_5479_; 
v___x_5479_ = lean_box(0);
v___y_5461_ = v___x_5479_;
goto v___jp_5460_;
}
else
{
lean_object* v___x_5480_; 
v___x_5480_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5461_ = v___x_5480_;
goto v___jp_5460_;
}
v___jp_5446_:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5449_ = l_Lean_Parser_maxPrec;
v___x_5450_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5451_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5452_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5453_ = l_Lean_Parser_antiquotExpr;
v___x_5454_ = l_Lean_Parser_andthen(v___x_5453_, v___y_5448_);
v___x_5455_ = l_Lean_Parser_andthen(v___x_5452_, v___x_5454_);
v___x_5456_ = l_Lean_Parser_andthen(v___x_5451_, v___x_5455_);
v___x_5457_ = l_Lean_Parser_andthen(v___x_5450_, v___x_5456_);
v___x_5458_ = l_Lean_Parser_atomic(v___x_5457_);
v___x_5459_ = l_Lean_Parser_leadingNode(v___y_5447_, v___x_5449_, v___x_5458_);
return v___x_5459_;
}
v___jp_5460_:
{
lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v_kind_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; uint8_t v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v_nameP_5476_; 
lean_inc(v___y_5461_);
v___x_5462_ = l_Lean_Name_append(v_kind_5443_, v___y_5461_);
v___x_5463_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5464_ = l_Lean_Name_append(v___x_5462_, v___x_5463_);
v___x_5465_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5466_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5467_ = lean_string_append(v___x_5466_, v_name_5442_);
v___x_5468_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5469_ = lean_string_append(v___x_5467_, v___x_5468_);
v___x_5470_ = l_Lean_Parser_checkNoWsBefore(v___x_5469_);
v___x_5471_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5472_ = 0;
v___x_5473_ = l_Lean_Parser_nonReservedSymbol(v_name_5442_, v___x_5472_);
v___x_5474_ = l_Lean_Parser_andthen(v___x_5471_, v___x_5473_);
v___x_5475_ = l_Lean_Parser_andthen(v___x_5470_, v___x_5474_);
v_nameP_5476_ = l_Lean_Parser_node(v___x_5465_, v___x_5475_);
if (v_anonymous_5444_ == 0)
{
v___y_5447_ = v_kind_5464_;
v___y_5448_ = v_nameP_5476_;
goto v___jp_5446_;
}
else
{
lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5477_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5478_ = l_Lean_Parser_orelse(v_nameP_5476_, v___x_5477_);
v___y_5447_ = v_kind_5464_;
v___y_5448_ = v___x_5478_;
goto v___jp_5446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5481_, lean_object* v_kind_5482_, lean_object* v_anonymous_5483_, lean_object* v_isPseudoKind_5484_){
_start:
{
uint8_t v_anonymous_boxed_5485_; uint8_t v_isPseudoKind_boxed_5486_; lean_object* v_res_5487_; 
v_anonymous_boxed_5485_ = lean_unbox(v_anonymous_5483_);
v_isPseudoKind_boxed_5486_ = lean_unbox(v_isPseudoKind_5484_);
v_res_5487_ = l_Lean_Parser_mkAntiquot(v_name_5481_, v_kind_5482_, v_anonymous_boxed_5485_, v_isPseudoKind_boxed_5486_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5495_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5496_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5497_ = l_Lean_addBuiltinDocString(v___x_5495_, v___x_5496_);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5498_){
_start:
{
lean_object* v_res_5499_; 
v_res_5499_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5500_, lean_object* v_p_5501_, uint8_t v_isCatAntiquot_5502_, lean_object* v_c_5503_, lean_object* v_s_5504_){
_start:
{
lean_object* v_toInputContext_5505_; lean_object* v_pos_5506_; lean_object* v_inputString_5507_; uint32_t v___x_5508_; uint32_t v___x_5509_; uint8_t v___x_5510_; 
v_toInputContext_5505_ = lean_ctor_get(v_c_5503_, 0);
v_pos_5506_ = lean_ctor_get(v_s_5504_, 2);
v_inputString_5507_ = lean_ctor_get(v_toInputContext_5505_, 0);
v___x_5508_ = lean_string_utf8_get(v_inputString_5507_, v_pos_5506_);
v___x_5509_ = 36;
v___x_5510_ = lean_uint32_dec_eq(v___x_5508_, v___x_5509_);
if (v___x_5510_ == 0)
{
lean_object* v___x_5511_; 
lean_dec_ref(v_antiquotP_5500_);
v___x_5511_ = lean_apply_2(v_p_5501_, v_c_5503_, v_s_5504_);
return v___x_5511_;
}
else
{
if (v_isCatAntiquot_5502_ == 0)
{
uint8_t v___x_5512_; lean_object* v___x_5513_; 
v___x_5512_ = 1;
v___x_5513_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5500_, v_p_5501_, v___x_5512_, v_c_5503_, v_s_5504_);
return v___x_5513_;
}
else
{
uint8_t v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = 0;
v___x_5515_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5500_, v_p_5501_, v___x_5514_, v_c_5503_, v_s_5504_);
return v___x_5515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5516_, lean_object* v_p_5517_, lean_object* v_isCatAntiquot_5518_, lean_object* v_c_5519_, lean_object* v_s_5520_){
_start:
{
uint8_t v_isCatAntiquot_boxed_5521_; lean_object* v_res_5522_; 
v_isCatAntiquot_boxed_5521_ = lean_unbox(v_isCatAntiquot_5518_);
v_res_5522_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5516_, v_p_5517_, v_isCatAntiquot_boxed_5521_, v_c_5519_, v_s_5520_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5523_, lean_object* v_p_5524_){
_start:
{
lean_object* v_info_5525_; lean_object* v_fn_5526_; lean_object* v_info_5527_; lean_object* v_fn_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5539_; 
v_info_5525_ = lean_ctor_get(v_antiquotP_5523_, 0);
lean_inc_ref(v_info_5525_);
v_fn_5526_ = lean_ctor_get(v_antiquotP_5523_, 1);
lean_inc_ref(v_fn_5526_);
lean_dec_ref(v_antiquotP_5523_);
v_info_5527_ = lean_ctor_get(v_p_5524_, 0);
v_fn_5528_ = lean_ctor_get(v_p_5524_, 1);
v_isSharedCheck_5539_ = !lean_is_exclusive(v_p_5524_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5530_ = v_p_5524_;
v_isShared_5531_ = v_isSharedCheck_5539_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_fn_5528_);
lean_inc(v_info_5527_);
lean_dec(v_p_5524_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5539_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5537_; 
v___x_5532_ = l_Lean_Parser_orelseInfo(v_info_5525_, v_info_5527_);
v___x_5533_ = 0;
v___x_5534_ = lean_box(v___x_5533_);
v___x_5535_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5535_, 0, v_fn_5526_);
lean_closure_set(v___x_5535_, 1, v_fn_5528_);
lean_closure_set(v___x_5535_, 2, v___x_5534_);
if (v_isShared_5531_ == 0)
{
lean_ctor_set(v___x_5530_, 1, v___x_5535_);
lean_ctor_set(v___x_5530_, 0, v___x_5532_);
v___x_5537_ = v___x_5530_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v___x_5535_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5547_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5548_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5549_ = l_Lean_addBuiltinDocString(v___x_5547_, v___x_5548_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5550_){
_start:
{
lean_object* v_res_5551_; 
v_res_5551_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5552_){
_start:
{
lean_object* v_fn_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5561_; 
v_fn_5553_ = lean_ctor_get(v_p_5552_, 1);
v_isSharedCheck_5561_ = !lean_is_exclusive(v_p_5552_);
if (v_isSharedCheck_5561_ == 0)
{
lean_object* v_unused_5562_; 
v_unused_5562_ = lean_ctor_get(v_p_5552_, 0);
lean_dec(v_unused_5562_);
v___x_5555_ = v_p_5552_;
v_isShared_5556_ = v_isSharedCheck_5561_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_fn_5553_);
lean_dec(v_p_5552_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5561_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5557_; lean_object* v___x_5559_; 
v___x_5557_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 0, v___x_5557_);
v___x_5559_ = v___x_5555_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5557_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v_fn_5553_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5566_; lean_object* v___x_5567_; 
v___x_5566_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5567_ = l_Lean_Parser_symbol(v___x_5566_);
return v___x_5567_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5568_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5569_ = l_Lean_Parser_symbol(v___x_5568_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5570_, lean_object* v_p_5571_, lean_object* v_suffix_5572_){
_start:
{
lean_object* v___x_5573_; lean_object* v_kind_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; 
v___x_5573_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5574_ = l_Lean_Name_append(v_kind_5570_, v___x_5573_);
v___x_5575_ = l_Lean_Parser_maxPrec;
v___x_5576_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5577_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5578_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5579_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5580_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5581_ = l_Lean_Parser_node(v___x_5580_, v_p_5571_);
v___x_5582_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5583_ = l_Lean_Parser_andthen(v___x_5582_, v_suffix_5572_);
v___x_5584_ = l_Lean_Parser_andthen(v___x_5581_, v___x_5583_);
v___x_5585_ = l_Lean_Parser_andthen(v___x_5579_, v___x_5584_);
v___x_5586_ = l_Lean_Parser_andthen(v___x_5578_, v___x_5585_);
v___x_5587_ = l_Lean_Parser_andthen(v___x_5577_, v___x_5586_);
v___x_5588_ = l_Lean_Parser_andthen(v___x_5576_, v___x_5587_);
v___x_5589_ = l_Lean_Parser_atomic(v___x_5588_);
v___x_5590_ = l_Lean_Parser_leadingNode(v_kind_5574_, v___x_5575_, v___x_5589_);
return v___x_5590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5598_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5599_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5600_ = l_Lean_addBuiltinDocString(v___x_5598_, v___x_5599_);
return v___x_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5606_, lean_object* v_suffix_5607_, lean_object* v_c_5608_, lean_object* v_s_5609_){
_start:
{
lean_object* v_pos_5610_; lean_object* v_iniSz_5611_; lean_object* v_s_5612_; lean_object* v_stxStack_5613_; lean_object* v_errorMsg_5614_; lean_object* v___x_5615_; uint8_t v___x_5616_; 
v_pos_5610_ = lean_ctor_get(v_s_5609_, 2);
lean_inc(v_pos_5610_);
v_iniSz_5611_ = l_Lean_Parser_ParserState_stackSize(v_s_5609_);
v_s_5612_ = lean_apply_2(v_suffix_5607_, v_c_5608_, v_s_5609_);
v_stxStack_5613_ = lean_ctor_get(v_s_5612_, 0);
lean_inc_ref(v_stxStack_5613_);
v_errorMsg_5614_ = lean_ctor_get(v_s_5612_, 4);
lean_inc(v_errorMsg_5614_);
v___x_5615_ = lean_box(0);
v___x_5616_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5614_, v___x_5615_);
lean_dec(v_errorMsg_5614_);
if (v___x_5616_ == 0)
{
lean_object* v___x_5617_; 
lean_dec_ref(v_stxStack_5613_);
lean_dec(v_kind_5606_);
v___x_5617_ = l_Lean_Parser_ParserState_restore(v_s_5612_, v_iniSz_5611_, v_pos_5610_);
lean_dec(v_iniSz_5611_);
return v___x_5617_;
}
else
{
lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; 
lean_dec(v_iniSz_5611_);
lean_dec(v_pos_5610_);
v___x_5618_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5619_ = l_Lean_Name_append(v_kind_5606_, v___x_5618_);
v___x_5620_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5613_);
lean_dec_ref(v_stxStack_5613_);
v___x_5621_ = lean_unsigned_to_nat(2u);
v___x_5622_ = lean_nat_sub(v___x_5620_, v___x_5621_);
lean_dec(v___x_5620_);
v___x_5623_ = l_Lean_Parser_ParserState_mkNode(v_s_5612_, v___x_5619_, v___x_5622_);
lean_dec(v___x_5622_);
return v___x_5623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5624_, lean_object* v_kind_5625_, lean_object* v_fn_5626_, lean_object* v_c_5627_, lean_object* v_s_5628_){
_start:
{
lean_object* v_s_5629_; lean_object* v_stxStack_5630_; lean_object* v_errorMsg_5631_; lean_object* v___x_5632_; uint8_t v___x_5633_; 
lean_inc_ref(v_c_5627_);
v_s_5629_ = lean_apply_2(v_fn_5624_, v_c_5627_, v_s_5628_);
v_stxStack_5630_ = lean_ctor_get(v_s_5629_, 0);
lean_inc_ref(v_stxStack_5630_);
v_errorMsg_5631_ = lean_ctor_get(v_s_5629_, 4);
lean_inc(v_errorMsg_5631_);
v___x_5632_ = lean_box(0);
v___x_5633_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5631_, v___x_5632_);
lean_dec(v_errorMsg_5631_);
if (v___x_5633_ == 0)
{
lean_dec_ref(v_stxStack_5630_);
lean_dec_ref(v_c_5627_);
lean_dec_ref(v_fn_5626_);
lean_dec(v_kind_5625_);
return v_s_5629_;
}
else
{
lean_object* v___x_5634_; uint8_t v___x_5635_; 
v___x_5634_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5630_);
lean_dec_ref(v_stxStack_5630_);
v___x_5635_ = l_Lean_Syntax_isAntiquots(v___x_5634_);
if (v___x_5635_ == 0)
{
lean_dec_ref(v_c_5627_);
lean_dec_ref(v_fn_5626_);
lean_dec(v_kind_5625_);
return v_s_5629_;
}
else
{
lean_object* v___x_5636_; 
v___x_5636_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5625_, v_fn_5626_, v_c_5627_, v_s_5629_);
return v___x_5636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5637_, lean_object* v_p_5638_, lean_object* v_suffix_5639_){
_start:
{
lean_object* v_info_5640_; lean_object* v_fn_5641_; lean_object* v_info_5642_; lean_object* v_fn_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5652_; 
v_info_5640_ = lean_ctor_get(v_p_5638_, 0);
lean_inc_ref(v_info_5640_);
v_fn_5641_ = lean_ctor_get(v_p_5638_, 1);
lean_inc_ref(v_fn_5641_);
lean_dec_ref(v_p_5638_);
v_info_5642_ = lean_ctor_get(v_suffix_5639_, 0);
v_fn_5643_ = lean_ctor_get(v_suffix_5639_, 1);
v_isSharedCheck_5652_ = !lean_is_exclusive(v_suffix_5639_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5645_ = v_suffix_5639_;
v_isShared_5646_ = v_isSharedCheck_5652_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_fn_5643_);
lean_inc(v_info_5642_);
lean_dec(v_suffix_5639_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5652_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___f_5647_; lean_object* v___x_5648_; lean_object* v___x_5650_; 
v___f_5647_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5647_, 0, v_fn_5641_);
lean_closure_set(v___f_5647_, 1, v_kind_5637_);
lean_closure_set(v___f_5647_, 2, v_fn_5643_);
v___x_5648_ = l_Lean_Parser_andthenInfo(v_info_5640_, v_info_5642_);
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 1, v___f_5647_);
lean_ctor_set(v___x_5645_, 0, v___x_5648_);
v___x_5650_ = v___x_5645_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___f_5647_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
v___x_5660_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5661_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5662_ = l_Lean_addBuiltinDocString(v___x_5660_, v___x_5661_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5663_){
_start:
{
lean_object* v_res_5664_; 
v_res_5664_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5665_, lean_object* v_p_5666_, lean_object* v_suffix_5667_){
_start:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; 
lean_inc_ref(v_p_5666_);
v___x_5668_ = l_Lean_Parser_withoutInfo(v_p_5666_);
lean_inc_ref(v_suffix_5667_);
lean_inc(v_kind_5665_);
v___x_5669_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5665_, v___x_5668_, v_suffix_5667_);
v___x_5670_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5665_, v_p_5666_, v_suffix_5667_);
v___x_5671_ = l_Lean_Parser_withAntiquot(v___x_5669_, v___x_5670_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5672_, lean_object* v_kind_5673_, lean_object* v_p_5674_, uint8_t v_anonymous_5675_){
_start:
{
uint8_t v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5676_ = 0;
lean_inc(v_kind_5673_);
v___x_5677_ = l_Lean_Parser_mkAntiquot(v_name_5672_, v_kind_5673_, v_anonymous_5675_, v___x_5676_);
v___x_5678_ = l_Lean_Parser_node(v_kind_5673_, v_p_5674_);
v___x_5679_ = l_Lean_Parser_withAntiquot(v___x_5677_, v___x_5678_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5680_, lean_object* v_kind_5681_, lean_object* v_p_5682_, lean_object* v_anonymous_5683_){
_start:
{
uint8_t v_anonymous_boxed_5684_; lean_object* v_res_5685_; 
v_anonymous_boxed_5684_ = lean_unbox(v_anonymous_5683_);
v_res_5685_ = l_Lean_Parser_nodeWithAntiquot(v_name_5680_, v_kind_5681_, v_p_5682_, v_anonymous_boxed_5684_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5690_, lean_object* v_sep_5691_){
_start:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v_str_5696_; lean_object* v_startInclusive_5697_; lean_object* v_endExclusive_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; 
v___x_5692_ = lean_unsigned_to_nat(0u);
v___x_5693_ = lean_string_utf8_byte_size(v_sep_5691_);
v___x_5694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5694_, 0, v_sep_5691_);
lean_ctor_set(v___x_5694_, 1, v___x_5692_);
lean_ctor_set(v___x_5694_, 2, v___x_5693_);
v___x_5695_ = l_String_Slice_trimAscii(v___x_5694_);
v_str_5696_ = lean_ctor_get(v___x_5695_, 0);
lean_inc_ref(v_str_5696_);
v_startInclusive_5697_ = lean_ctor_get(v___x_5695_, 1);
lean_inc(v_startInclusive_5697_);
v_endExclusive_5698_ = lean_ctor_get(v___x_5695_, 2);
lean_inc(v_endExclusive_5698_);
lean_dec_ref(v___x_5695_);
v___x_5699_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5700_ = lean_string_utf8_extract_fast(v_str_5696_, v_startInclusive_5697_, v_endExclusive_5698_);
lean_dec(v_endExclusive_5698_);
lean_dec(v_startInclusive_5697_);
lean_dec_ref(v_str_5696_);
v___x_5701_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5702_ = lean_string_append(v___x_5700_, v___x_5701_);
v___x_5703_ = l_Lean_Parser_symbol(v___x_5702_);
v___x_5704_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5699_, v_p_5690_, v___x_5703_);
return v___x_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5705_, lean_object* v_sep_5706_, lean_object* v_psep_5707_, uint8_t v_allowTrailingSep_5708_){
_start:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5709_ = l_Lean_Parser_sepByElemParser(v_p_5705_, v_sep_5706_);
v___x_5710_ = l_Lean_Parser_sepByNoAntiquot(v___x_5709_, v_psep_5707_, v_allowTrailingSep_5708_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5711_, lean_object* v_sep_5712_, lean_object* v_psep_5713_, lean_object* v_allowTrailingSep_5714_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5715_; lean_object* v_res_5716_; 
v_allowTrailingSep_boxed_5715_ = lean_unbox(v_allowTrailingSep_5714_);
v_res_5716_ = l_Lean_Parser_sepBy(v_p_5711_, v_sep_5712_, v_psep_5713_, v_allowTrailingSep_boxed_5715_);
return v_res_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5717_, lean_object* v_sep_5718_, lean_object* v_psep_5719_, uint8_t v_allowTrailingSep_5720_){
_start:
{
lean_object* v___x_5721_; lean_object* v___x_5722_; 
v___x_5721_ = l_Lean_Parser_sepByElemParser(v_p_5717_, v_sep_5718_);
v___x_5722_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5721_, v_psep_5719_, v_allowTrailingSep_5720_);
return v___x_5722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5723_, lean_object* v_sep_5724_, lean_object* v_psep_5725_, lean_object* v_allowTrailingSep_5726_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5727_; lean_object* v_res_5728_; 
v_allowTrailingSep_boxed_5727_ = lean_unbox(v_allowTrailingSep_5726_);
v_res_5728_ = l_Lean_Parser_sepBy1(v_p_5723_, v_sep_5724_, v_psep_5725_, v_allowTrailingSep_boxed_5727_);
return v_res_5728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5729_, lean_object* v_iniSz_5730_){
_start:
{
lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5731_ = l_Lean_Parser_ParserState_stackSize(v_s_5729_);
v___x_5732_ = lean_unsigned_to_nat(1u);
v___x_5733_ = lean_nat_add(v_iniSz_5730_, v___x_5732_);
v___x_5734_ = lean_nat_dec_eq(v___x_5731_, v___x_5733_);
lean_dec(v___x_5733_);
lean_dec(v___x_5731_);
if (v___x_5734_ == 0)
{
lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5735_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5736_ = l_Lean_Parser_ParserState_mkNode(v_s_5729_, v___x_5735_, v_iniSz_5730_);
return v___x_5736_;
}
else
{
return v_s_5729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5737_, lean_object* v_iniSz_5738_){
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5737_, v_iniSz_5738_);
lean_dec(v_iniSz_5738_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5740_, lean_object* v_tables_5741_, uint8_t v_behavior_5742_, lean_object* v_c_5743_, lean_object* v_s_5744_){
_start:
{
lean_object* v_leadingTable_5745_; lean_object* v_leadingParsers_5746_; lean_object* v_iniSz_5747_; lean_object* v___x_5748_; lean_object* v_fst_5749_; lean_object* v_snd_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5772_; 
v_leadingTable_5745_ = lean_ctor_get(v_tables_5741_, 0);
lean_inc(v_leadingTable_5745_);
v_leadingParsers_5746_ = lean_ctor_get(v_tables_5741_, 1);
lean_inc(v_leadingParsers_5746_);
lean_dec_ref(v_tables_5741_);
v_iniSz_5747_ = l_Lean_Parser_ParserState_stackSize(v_s_5744_);
lean_inc_ref(v_c_5743_);
v___x_5748_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5745_, v_c_5743_, v_s_5744_, v_behavior_5742_);
lean_dec(v_leadingTable_5745_);
v_fst_5749_ = lean_ctor_get(v___x_5748_, 0);
v_snd_5750_ = lean_ctor_get(v___x_5748_, 1);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5752_ = v___x_5748_;
v_isShared_5753_ = v_isSharedCheck_5772_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_snd_5750_);
lean_inc(v_fst_5749_);
lean_dec(v___x_5748_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5772_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v_errorMsg_5754_; lean_object* v___x_5755_; uint8_t v___x_5756_; 
v_errorMsg_5754_ = lean_ctor_get(v_fst_5749_, 4);
v___x_5755_ = lean_box(0);
v___x_5756_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5754_, v___x_5755_);
if (v___x_5756_ == 0)
{
lean_del_object(v___x_5752_);
lean_dec(v_snd_5750_);
lean_dec(v_iniSz_5747_);
lean_dec(v_leadingParsers_5746_);
lean_dec_ref(v_c_5743_);
lean_dec(v_kind_5740_);
return v_fst_5749_;
}
else
{
lean_object* v_ps_5757_; uint8_t v___x_5758_; 
v_ps_5757_ = l_List_appendTR___redArg(v_leadingParsers_5746_, v_snd_5750_);
v___x_5758_ = l_List_isEmpty___redArg(v_ps_5757_);
if (v___x_5758_ == 0)
{
lean_object* v_s_5759_; lean_object* v___x_5760_; 
lean_del_object(v___x_5752_);
lean_dec(v_kind_5740_);
v_s_5759_ = l_Lean_Parser_longestMatchFn(v___x_5755_, v_ps_5757_, v_c_5743_, v_fst_5749_);
v___x_5760_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5759_, v_iniSz_5747_);
lean_dec(v_iniSz_5747_);
return v___x_5760_;
}
else
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5764_; 
lean_dec(v_ps_5757_);
lean_dec(v_iniSz_5747_);
v___x_5761_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5740_, v___x_5758_);
v___x_5762_ = lean_box(0);
lean_inc_ref(v___x_5761_);
if (v_isShared_5753_ == 0)
{
lean_ctor_set_tag(v___x_5752_, 1);
lean_ctor_set(v___x_5752_, 1, v___x_5762_);
lean_ctor_set(v___x_5752_, 0, v___x_5761_);
v___x_5764_ = v___x_5752_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v___x_5762_);
v___x_5764_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
lean_object* v_s_5765_; lean_object* v_errorMsg_5769_; uint8_t v___x_5770_; 
v_s_5765_ = l_Lean_Parser_tokenFn(v___x_5764_, v_c_5743_, v_fst_5749_);
v_errorMsg_5769_ = lean_ctor_get(v_s_5765_, 4);
lean_inc(v_errorMsg_5769_);
v___x_5770_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5769_, v___x_5755_);
lean_dec(v_errorMsg_5769_);
if (v___x_5770_ == 0)
{
if (v___x_5758_ == 0)
{
goto v___jp_5766_;
}
else
{
lean_dec_ref(v___x_5761_);
return v_s_5765_;
}
}
else
{
goto v___jp_5766_;
}
v___jp_5766_:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___x_5767_ = lean_unsigned_to_nat(0u);
v___x_5768_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5765_, v___x_5761_, v___x_5767_);
return v___x_5768_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5773_, lean_object* v_tables_5774_, lean_object* v_behavior_5775_, lean_object* v_c_5776_, lean_object* v_s_5777_){
_start:
{
uint8_t v_behavior_boxed_5778_; lean_object* v_res_5779_; 
v_behavior_boxed_5778_ = lean_unbox(v_behavior_5775_);
v_res_5779_ = l_Lean_Parser_leadingParserAux(v_kind_5773_, v_tables_5774_, v_behavior_boxed_5778_, v_c_5776_, v_s_5777_);
return v_res_5779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5780_, lean_object* v_tables_5781_, uint8_t v_behavior_5782_, lean_object* v_antiquotParser_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_){
_start:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; uint8_t v___x_5788_; lean_object* v___x_5789_; 
v___x_5786_ = lean_box(v_behavior_5782_);
v___x_5787_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5787_, 0, v_kind_5780_);
lean_closure_set(v___x_5787_, 1, v_tables_5781_);
lean_closure_set(v___x_5787_, 2, v___x_5786_);
v___x_5788_ = 1;
v___x_5789_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5783_, v___x_5787_, v___x_5788_, v_a_5784_, v_a_5785_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5790_, lean_object* v_tables_5791_, lean_object* v_behavior_5792_, lean_object* v_antiquotParser_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_){
_start:
{
uint8_t v_behavior_boxed_5796_; lean_object* v_res_5797_; 
v_behavior_boxed_5796_ = lean_unbox(v_behavior_5792_);
v_res_5797_ = l_Lean_Parser_leadingParser(v_kind_5790_, v_tables_5791_, v_behavior_boxed_5796_, v_antiquotParser_5793_, v_a_5794_, v_a_5795_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5798_, lean_object* v_left_5799_, lean_object* v_ps_5800_, lean_object* v_c_5801_, lean_object* v_s_5802_){
_start:
{
lean_object* v_trailingParsers_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
v_trailingParsers_5803_ = lean_ctor_get(v_tables_5798_, 3);
lean_inc(v_trailingParsers_5803_);
lean_dec_ref(v_tables_5798_);
v___x_5804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5804_, 0, v_left_5799_);
v___x_5805_ = l_List_appendTR___redArg(v_ps_5800_, v_trailingParsers_5803_);
v___x_5806_ = l_Lean_Parser_longestMatchFn(v___x_5804_, v___x_5805_, v_c_5801_, v_s_5802_);
return v___x_5806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5807_, lean_object* v_c_5808_, lean_object* v_s_5809_){
_start:
{
lean_object* v_pos_5810_; lean_object* v_trailingTable_5811_; lean_object* v_trailingParsers_5812_; lean_object* v_iniSz_5813_; uint8_t v___x_5814_; lean_object* v___x_5815_; lean_object* v_fst_5816_; lean_object* v_snd_5817_; lean_object* v_stxStack_5818_; lean_object* v_errorMsg_5819_; uint8_t v___y_5821_; lean_object* v___x_5835_; uint8_t v___x_5836_; 
v_pos_5810_ = lean_ctor_get(v_s_5809_, 2);
lean_inc(v_pos_5810_);
v_trailingTable_5811_ = lean_ctor_get(v_tables_5807_, 2);
v_trailingParsers_5812_ = lean_ctor_get(v_tables_5807_, 3);
v_iniSz_5813_ = l_Lean_Parser_ParserState_stackSize(v_s_5809_);
v___x_5814_ = 0;
lean_inc_ref(v_c_5808_);
v___x_5815_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5811_, v_c_5808_, v_s_5809_, v___x_5814_);
v_fst_5816_ = lean_ctor_get(v___x_5815_, 0);
lean_inc(v_fst_5816_);
v_snd_5817_ = lean_ctor_get(v___x_5815_, 1);
lean_inc(v_snd_5817_);
lean_dec_ref(v___x_5815_);
v_stxStack_5818_ = lean_ctor_get(v_fst_5816_, 0);
v_errorMsg_5819_ = lean_ctor_get(v_fst_5816_, 4);
v___x_5835_ = lean_box(0);
v___x_5836_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5819_, v___x_5835_);
if (v___x_5836_ == 0)
{
lean_object* v___x_5837_; 
lean_dec(v_snd_5817_);
lean_dec_ref(v_c_5808_);
lean_dec_ref(v_tables_5807_);
v___x_5837_ = l_Lean_Parser_ParserState_restore(v_fst_5816_, v_iniSz_5813_, v_pos_5810_);
lean_dec(v_iniSz_5813_);
return v___x_5837_;
}
else
{
uint8_t v___x_5838_; 
v___x_5838_ = l_List_isEmpty___redArg(v_snd_5817_);
if (v___x_5838_ == 0)
{
v___y_5821_ = v___x_5838_;
goto v___jp_5820_;
}
else
{
uint8_t v___x_5839_; 
v___x_5839_ = l_List_isEmpty___redArg(v_trailingParsers_5812_);
v___y_5821_ = v___x_5839_;
goto v___jp_5820_;
}
}
v___jp_5820_:
{
if (v___y_5821_ == 0)
{
lean_object* v_left_5822_; lean_object* v_s_5823_; lean_object* v_s_5824_; lean_object* v_pos_5825_; lean_object* v_errorMsg_5826_; lean_object* v___x_5827_; uint8_t v___x_5828_; 
v_left_5822_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5818_);
v_s_5823_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5816_);
lean_inc_ref(v_c_5808_);
lean_inc(v_left_5822_);
lean_inc_ref(v_tables_5807_);
v_s_5824_ = l_Lean_Parser_trailingLoopStep(v_tables_5807_, v_left_5822_, v_snd_5817_, v_c_5808_, v_s_5823_);
v_pos_5825_ = lean_ctor_get(v_s_5824_, 2);
lean_inc(v_pos_5825_);
v_errorMsg_5826_ = lean_ctor_get(v_s_5824_, 4);
lean_inc(v_errorMsg_5826_);
v___x_5827_ = lean_box(0);
v___x_5828_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5826_, v___x_5827_);
lean_dec(v_errorMsg_5826_);
if (v___x_5828_ == 0)
{
uint8_t v___x_5829_; 
lean_dec_ref(v_c_5808_);
lean_dec_ref(v_tables_5807_);
v___x_5829_ = lean_nat_dec_eq(v_pos_5825_, v_pos_5810_);
lean_dec(v_pos_5825_);
if (v___x_5829_ == 0)
{
lean_dec(v_left_5822_);
lean_dec(v_iniSz_5813_);
lean_dec(v_pos_5810_);
return v_s_5824_;
}
else
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5830_ = lean_unsigned_to_nat(1u);
v___x_5831_ = lean_nat_sub(v_iniSz_5813_, v___x_5830_);
lean_dec(v_iniSz_5813_);
v___x_5832_ = l_Lean_Parser_ParserState_restore(v_s_5824_, v___x_5831_, v_pos_5810_);
lean_dec(v___x_5831_);
v___x_5833_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5832_, v_left_5822_);
return v___x_5833_;
}
}
else
{
lean_dec(v_pos_5825_);
lean_dec(v_left_5822_);
lean_dec(v_iniSz_5813_);
lean_dec(v_pos_5810_);
v_s_5809_ = v_s_5824_;
goto _start;
}
}
else
{
lean_dec(v_snd_5817_);
lean_dec(v_iniSz_5813_);
lean_dec(v_pos_5810_);
lean_dec_ref(v_c_5808_);
lean_dec_ref(v_tables_5807_);
return v_fst_5816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5840_, lean_object* v_tables_5841_, uint8_t v_behavior_5842_, lean_object* v_antiquotParser_5843_, lean_object* v_c_5844_, lean_object* v_s_5845_){
_start:
{
lean_object* v_s_5846_; lean_object* v_errorMsg_5847_; lean_object* v___x_5848_; uint8_t v___x_5849_; 
lean_inc_ref(v_c_5844_);
lean_inc_ref(v_tables_5841_);
v_s_5846_ = l_Lean_Parser_leadingParser(v_kind_5840_, v_tables_5841_, v_behavior_5842_, v_antiquotParser_5843_, v_c_5844_, v_s_5845_);
v_errorMsg_5847_ = lean_ctor_get(v_s_5846_, 4);
lean_inc(v_errorMsg_5847_);
v___x_5848_ = lean_box(0);
v___x_5849_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5847_, v___x_5848_);
lean_dec(v_errorMsg_5847_);
if (v___x_5849_ == 0)
{
lean_dec_ref(v_c_5844_);
lean_dec_ref(v_tables_5841_);
return v_s_5846_;
}
else
{
lean_object* v___x_5850_; 
v___x_5850_ = l_Lean_Parser_trailingLoop(v_tables_5841_, v_c_5844_, v_s_5846_);
return v___x_5850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5851_, lean_object* v_tables_5852_, lean_object* v_behavior_5853_, lean_object* v_antiquotParser_5854_, lean_object* v_c_5855_, lean_object* v_s_5856_){
_start:
{
uint8_t v_behavior_boxed_5857_; lean_object* v_res_5858_; 
v_behavior_boxed_5857_ = lean_unbox(v_behavior_5853_);
v_res_5858_ = l_Lean_Parser_prattParser(v_kind_5851_, v_tables_5852_, v_behavior_boxed_5857_, v_antiquotParser_5854_, v_c_5855_, v_s_5856_);
return v_res_5858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5863_, lean_object* v_s_5864_){
_start:
{
lean_object* v_toInputContext_5865_; lean_object* v_pos_5866_; lean_object* v_inputString_5867_; lean_object* v___f_5868_; lean_object* v_initStackSz_5869_; uint32_t v_curr_5874_; uint8_t v___y_5876_; uint32_t v___x_5882_; uint8_t v___x_5883_; 
v_toInputContext_5865_ = lean_ctor_get(v_c_5863_, 0);
v_pos_5866_ = lean_ctor_get(v_s_5864_, 2);
lean_inc(v_pos_5866_);
v_inputString_5867_ = lean_ctor_get(v_toInputContext_5865_, 0);
v___f_5868_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_initStackSz_5869_ = l_Lean_Parser_ParserState_stackSize(v_s_5864_);
v_curr_5874_ = lean_string_utf8_get(v_inputString_5867_, v_pos_5866_);
v___x_5882_ = 48;
v___x_5883_ = lean_uint32_dec_le(v___x_5882_, v_curr_5874_);
if (v___x_5883_ == 0)
{
v___y_5876_ = v___x_5883_;
goto v___jp_5875_;
}
else
{
uint32_t v___x_5884_; uint8_t v___x_5885_; 
v___x_5884_ = 57;
v___x_5885_ = lean_uint32_dec_le(v_curr_5874_, v___x_5884_);
v___y_5876_ = v___x_5885_;
goto v___jp_5875_;
}
v___jp_5870_:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; 
v___x_5871_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5872_, 0, v_initStackSz_5869_);
v___x_5873_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5864_, v___x_5871_, v_pos_5866_, v___x_5872_);
lean_dec_ref_known(v___x_5872_, 1);
return v___x_5873_;
}
v___jp_5875_:
{
if (v___y_5876_ == 0)
{
lean_dec_ref(v_c_5863_);
goto v___jp_5870_;
}
else
{
uint32_t v___x_5877_; uint8_t v___x_5878_; 
v___x_5877_ = 48;
v___x_5878_ = lean_uint32_dec_eq(v_curr_5874_, v___x_5877_);
if (v___x_5878_ == 0)
{
lean_object* v_s_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
lean_dec(v_initStackSz_5869_);
v_s_5879_ = l_Lean_Parser_takeWhileFn(v___f_5868_, v_c_5863_, v_s_5864_);
v___x_5880_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5881_ = l_Lean_Parser_mkNodeToken(v___x_5880_, v_pos_5866_, v___y_5876_, v_c_5863_, v_s_5879_);
return v___x_5881_;
}
else
{
lean_dec_ref(v_c_5863_);
goto v___jp_5870_;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5886_; uint8_t v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5886_ = 0;
v___x_5887_ = 1;
v___x_5888_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5889_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5890_ = l_Lean_Parser_mkAntiquot(v___x_5889_, v___x_5888_, v___x_5887_, v___x_5886_);
return v___x_5890_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___x_5891_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5892_ = l_Lean_Parser_mkAtomicInfo(v___x_5891_);
return v___x_5892_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5893_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5894_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5894_);
lean_ctor_set(v___x_5895_, 1, v___x_5893_);
return v___x_5895_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; 
v___x_5896_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5897_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5898_ = l_Lean_Parser_withAntiquot(v___x_5897_, v___x_5896_);
return v___x_5898_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5899_; 
v___x_5899_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5900_, lean_object* v_s_5901_){
_start:
{
lean_inc_ref(v_s_5901_);
return v_s_5901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5902_, lean_object* v_s_5903_){
_start:
{
lean_object* v_res_5904_; 
v_res_5904_ = l_Lean_Parser_skip___lam__0(v_x_5902_, v_s_5903_);
lean_dec_ref(v_s_5903_);
lean_dec_ref(v_x_5902_);
return v_res_5904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5910_, lean_object* v_s_5911_, lean_object* v_f_5912_, lean_object* v_b_5913_){
_start:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; uint8_t v___x_5917_; 
v___x_5914_ = l_Lean_Syntax_getArgs(v_s_5911_);
v___x_5915_ = lean_unsigned_to_nat(0u);
v___x_5916_ = lean_array_get_size(v___x_5914_);
v___x_5917_ = lean_nat_dec_lt(v___x_5915_, v___x_5916_);
if (v___x_5917_ == 0)
{
lean_object* v_toApplicative_5918_; lean_object* v_toPure_5919_; lean_object* v___x_5920_; 
lean_dec_ref(v___x_5914_);
lean_dec(v_f_5912_);
v_toApplicative_5918_ = lean_ctor_get(v_inst_5910_, 0);
lean_inc_ref(v_toApplicative_5918_);
lean_dec_ref(v_inst_5910_);
v_toPure_5919_ = lean_ctor_get(v_toApplicative_5918_, 1);
lean_inc(v_toPure_5919_);
lean_dec_ref(v_toApplicative_5918_);
v___x_5920_ = lean_apply_2(v_toPure_5919_, lean_box(0), v_b_5913_);
return v___x_5920_;
}
else
{
lean_object* v___x_5921_; uint8_t v___x_5922_; 
v___x_5921_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5921_, 0, lean_box(0));
lean_closure_set(v___x_5921_, 1, lean_box(0));
lean_closure_set(v___x_5921_, 2, lean_box(0));
lean_closure_set(v___x_5921_, 3, v_f_5912_);
v___x_5922_ = lean_nat_dec_le(v___x_5916_, v___x_5916_);
if (v___x_5922_ == 0)
{
if (v___x_5917_ == 0)
{
lean_object* v_toApplicative_5923_; lean_object* v_toPure_5924_; lean_object* v___x_5925_; 
lean_dec_ref(v___x_5921_);
lean_dec_ref(v___x_5914_);
v_toApplicative_5923_ = lean_ctor_get(v_inst_5910_, 0);
lean_inc_ref(v_toApplicative_5923_);
lean_dec_ref(v_inst_5910_);
v_toPure_5924_ = lean_ctor_get(v_toApplicative_5923_, 1);
lean_inc(v_toPure_5924_);
lean_dec_ref(v_toApplicative_5923_);
v___x_5925_ = lean_apply_2(v_toPure_5924_, lean_box(0), v_b_5913_);
return v___x_5925_;
}
else
{
size_t v___x_5926_; size_t v___x_5927_; lean_object* v___x_5928_; 
v___x_5926_ = ((size_t)0ULL);
v___x_5927_ = lean_usize_of_nat(v___x_5916_);
v___x_5928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5910_, v___x_5921_, v___x_5914_, v___x_5926_, v___x_5927_, v_b_5913_);
return v___x_5928_;
}
}
else
{
size_t v___x_5929_; size_t v___x_5930_; lean_object* v___x_5931_; 
v___x_5929_ = ((size_t)0ULL);
v___x_5930_ = lean_usize_of_nat(v___x_5916_);
v___x_5931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5910_, v___x_5921_, v___x_5914_, v___x_5929_, v___x_5930_, v_b_5913_);
return v___x_5931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5932_, lean_object* v_s_5933_, lean_object* v_f_5934_, lean_object* v_b_5935_){
_start:
{
lean_object* v_res_5936_; 
v_res_5936_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5932_, v_s_5933_, v_f_5934_, v_b_5935_);
lean_dec(v_s_5933_);
return v_res_5936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5937_, lean_object* v_inst_5938_, lean_object* v_00_u03b2_5939_, lean_object* v_s_5940_, lean_object* v_f_5941_, lean_object* v_b_5942_){
_start:
{
lean_object* v___x_5943_; 
v___x_5943_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5938_, v_s_5940_, v_f_5941_, v_b_5942_);
return v___x_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5944_, lean_object* v_inst_5945_, lean_object* v_00_u03b2_5946_, lean_object* v_s_5947_, lean_object* v_f_5948_, lean_object* v_b_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_Lean_Syntax_foldArgsM(v_m_5944_, v_inst_5945_, v_00_u03b2_5946_, v_s_5947_, v_f_5948_, v_b_5949_);
lean_dec(v_s_5947_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5951_, lean_object* v_x1_5952_, lean_object* v_x2_5953_){
_start:
{
lean_object* v___x_5954_; 
v___x_5954_ = lean_apply_2(v_f_5951_, v_x1_5952_, v_x2_5953_);
return v___x_5954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5955_, lean_object* v_as_5956_, size_t v_i_5957_, size_t v_stop_5958_, lean_object* v_b_5959_){
_start:
{
uint8_t v___x_5960_; 
v___x_5960_ = lean_usize_dec_eq(v_i_5957_, v_stop_5958_);
if (v___x_5960_ == 0)
{
lean_object* v___x_5961_; lean_object* v___x_5962_; size_t v___x_5963_; size_t v___x_5964_; 
v___x_5961_ = lean_array_uget_borrowed(v_as_5956_, v_i_5957_);
lean_inc(v_f_5955_);
lean_inc(v___x_5961_);
v___x_5962_ = lean_apply_2(v_f_5955_, v___x_5961_, v_b_5959_);
v___x_5963_ = ((size_t)1ULL);
v___x_5964_ = lean_usize_add(v_i_5957_, v___x_5963_);
v_i_5957_ = v___x_5964_;
v_b_5959_ = v___x_5962_;
goto _start;
}
else
{
lean_dec(v_f_5955_);
return v_b_5959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5966_, lean_object* v_as_5967_, lean_object* v_i_5968_, lean_object* v_stop_5969_, lean_object* v_b_5970_){
_start:
{
size_t v_i_boxed_5971_; size_t v_stop_boxed_5972_; lean_object* v_res_5973_; 
v_i_boxed_5971_ = lean_unbox_usize(v_i_5968_);
lean_dec(v_i_5968_);
v_stop_boxed_5972_ = lean_unbox_usize(v_stop_5969_);
lean_dec(v_stop_5969_);
v_res_5973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5966_, v_as_5967_, v_i_boxed_5971_, v_stop_boxed_5972_, v_b_5970_);
lean_dec_ref(v_as_5967_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5974_, lean_object* v_f_5975_, lean_object* v_b_5976_){
_start:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; uint8_t v___x_5980_; 
v___x_5977_ = l_Lean_Syntax_getArgs(v_s_5974_);
v___x_5978_ = lean_unsigned_to_nat(0u);
v___x_5979_ = lean_array_get_size(v___x_5977_);
v___x_5980_ = lean_nat_dec_lt(v___x_5978_, v___x_5979_);
if (v___x_5980_ == 0)
{
lean_dec_ref(v___x_5977_);
lean_dec(v_f_5975_);
return v_b_5976_;
}
else
{
uint8_t v___x_5981_; 
v___x_5981_ = lean_nat_dec_le(v___x_5979_, v___x_5979_);
if (v___x_5981_ == 0)
{
if (v___x_5980_ == 0)
{
lean_dec_ref(v___x_5977_);
lean_dec(v_f_5975_);
return v_b_5976_;
}
else
{
size_t v___x_5982_; size_t v___x_5983_; lean_object* v___x_5984_; 
v___x_5982_ = ((size_t)0ULL);
v___x_5983_ = lean_usize_of_nat(v___x_5979_);
v___x_5984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5975_, v___x_5977_, v___x_5982_, v___x_5983_, v_b_5976_);
lean_dec_ref(v___x_5977_);
return v___x_5984_;
}
}
else
{
size_t v___x_5985_; size_t v___x_5986_; lean_object* v___x_5987_; 
v___x_5985_ = ((size_t)0ULL);
v___x_5986_ = lean_usize_of_nat(v___x_5979_);
v___x_5987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5975_, v___x_5977_, v___x_5985_, v___x_5986_, v_b_5976_);
lean_dec_ref(v___x_5977_);
return v___x_5987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5988_, lean_object* v_f_5989_, lean_object* v_b_5990_){
_start:
{
lean_object* v_res_5991_; 
v_res_5991_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5988_, v_f_5989_, v_b_5990_);
lean_dec(v_s_5988_);
return v_res_5991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5992_, lean_object* v_f_5993_, lean_object* v_b_5994_){
_start:
{
lean_object* v___f_5995_; lean_object* v___x_5996_; 
v___f_5995_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5995_, 0, v_f_5993_);
v___x_5996_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5992_, v___f_5995_, v_b_5994_);
return v___x_5996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_5997_, lean_object* v_f_5998_, lean_object* v_b_5999_){
_start:
{
lean_object* v_res_6000_; 
v_res_6000_ = l_Lean_Syntax_foldArgs___redArg(v_s_5997_, v_f_5998_, v_b_5999_);
lean_dec(v_s_5997_);
return v_res_6000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_6001_, lean_object* v_s_6002_, lean_object* v_f_6003_, lean_object* v_b_6004_){
_start:
{
lean_object* v___x_6005_; 
v___x_6005_ = l_Lean_Syntax_foldArgs___redArg(v_s_6002_, v_f_6003_, v_b_6004_);
return v___x_6005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_6006_, lean_object* v_s_6007_, lean_object* v_f_6008_, lean_object* v_b_6009_){
_start:
{
lean_object* v_res_6010_; 
v_res_6010_ = l_Lean_Syntax_foldArgs(v_00_u03b2_6006_, v_s_6007_, v_f_6008_, v_b_6009_);
lean_dec(v_s_6007_);
return v_res_6010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_6011_, lean_object* v_s_6012_, lean_object* v_f_6013_, lean_object* v_b_6014_){
_start:
{
lean_object* v___x_6015_; 
v___x_6015_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_6012_, v_f_6013_, v_b_6014_);
return v___x_6015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_6016_, lean_object* v_s_6017_, lean_object* v_f_6018_, lean_object* v_b_6019_){
_start:
{
lean_object* v_res_6020_; 
v_res_6020_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_6016_, v_s_6017_, v_f_6018_, v_b_6019_);
lean_dec(v_s_6017_);
return v_res_6020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_6021_, lean_object* v_f_6022_, lean_object* v_as_6023_, size_t v_i_6024_, size_t v_stop_6025_, lean_object* v_b_6026_){
_start:
{
lean_object* v___x_6027_; 
v___x_6027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_6022_, v_as_6023_, v_i_6024_, v_stop_6025_, v_b_6026_);
return v___x_6027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_6028_, lean_object* v_f_6029_, lean_object* v_as_6030_, lean_object* v_i_6031_, lean_object* v_stop_6032_, lean_object* v_b_6033_){
_start:
{
size_t v_i_boxed_6034_; size_t v_stop_boxed_6035_; lean_object* v_res_6036_; 
v_i_boxed_6034_ = lean_unbox_usize(v_i_6031_);
lean_dec(v_i_6031_);
v_stop_boxed_6035_ = lean_unbox_usize(v_stop_6032_);
lean_dec(v_stop_6032_);
v_res_6036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_6028_, v_f_6029_, v_as_6030_, v_i_boxed_6034_, v_stop_boxed_6035_, v_b_6033_);
lean_dec_ref(v_as_6030_);
return v_res_6036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_6037_, lean_object* v_s_6038_, lean_object* v_x_6039_){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = lean_apply_1(v_f_6037_, v_s_6038_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_6041_, lean_object* v_s_6042_, lean_object* v_f_6043_){
_start:
{
lean_object* v___f_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___f_6044_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6044_, 0, v_f_6043_);
v___x_6045_ = lean_box(0);
v___x_6046_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6041_, v_s_6042_, v___f_6044_, v___x_6045_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_6047_, lean_object* v_s_6048_, lean_object* v_f_6049_){
_start:
{
lean_object* v_res_6050_; 
v_res_6050_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6047_, v_s_6048_, v_f_6049_);
lean_dec(v_s_6048_);
return v_res_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_6051_, lean_object* v_inst_6052_, lean_object* v_s_6053_, lean_object* v_f_6054_){
_start:
{
lean_object* v___x_6055_; 
v___x_6055_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6052_, v_s_6053_, v_f_6054_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_6056_, lean_object* v_inst_6057_, lean_object* v_s_6058_, lean_object* v_f_6059_){
_start:
{
lean_object* v_res_6060_; 
v_res_6060_ = l_Lean_Syntax_forArgsM(v_m_6056_, v_inst_6057_, v_s_6058_, v_f_6059_);
lean_dec(v_s_6058_);
return v_res_6060_;
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
