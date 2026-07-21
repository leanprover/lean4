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
lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* v_stxStack_610_; lean_object* v_lhsPrec_611_; lean_object* v_pos_612_; lean_object* v_cache_613_; lean_object* v_errorMsg_614_; lean_object* v_recoveredErrors_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_633_; 
v_stxStack_610_ = lean_ctor_get(v_s_606_, 0);
v_lhsPrec_611_ = lean_ctor_get(v_s_606_, 1);
v_pos_612_ = lean_ctor_get(v_s_606_, 2);
v_cache_613_ = lean_ctor_get(v_s_606_, 3);
v_errorMsg_614_ = lean_ctor_get(v_s_606_, 4);
v_recoveredErrors_615_ = lean_ctor_get(v_s_606_, 5);
v_isSharedCheck_633_ = !lean_is_exclusive(v_s_606_);
if (v_isSharedCheck_633_ == 0)
{
v___x_617_ = v_s_606_;
v_isShared_618_ = v_isSharedCheck_633_;
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
v_isShared_618_ = v_isSharedCheck_633_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_raw_619_; lean_object* v_drop_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_632_; 
v_raw_619_ = lean_ctor_get(v_stxStack_610_, 0);
v_drop_620_ = lean_ctor_get(v_stxStack_610_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_stxStack_610_);
if (v_isSharedCheck_632_ == 0)
{
v___x_622_ = v_stxStack_610_;
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_drop_620_);
lean_inc(v_raw_619_);
lean_dec(v_stxStack_610_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_624_ = l_Lean_Syntax_getArgs(v_stx_605_);
lean_dec(v_stx_605_);
v___x_625_ = l_Array_append___redArg(v_raw_619_, v___x_624_);
lean_dec_ref(v___x_624_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_drop_620_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_627_);
v___x_629_ = v___x_617_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_lhsPrec_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_pos_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_cache_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v_errorMsg_614_);
lean_ctor_set(v_reuseFailAlloc_630_, 5, v_recoveredErrors_615_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* v_p_634_, lean_object* v_q_635_, uint8_t v_antiquotBehavior_636_, lean_object* v_c_637_, lean_object* v_s_638_){
_start:
{
lean_object* v_pos_639_; lean_object* v_iniSz_640_; lean_object* v_s_641_; lean_object* v_errorMsg_642_; 
v_pos_639_ = lean_ctor_get(v_s_638_, 2);
lean_inc(v_pos_639_);
v_iniSz_640_ = l_Lean_Parser_ParserState_stackSize(v_s_638_);
lean_inc_ref(v_c_637_);
v_s_641_ = lean_apply_2(v_p_634_, v_c_637_, v_s_638_);
v_errorMsg_642_ = lean_ctor_get(v_s_641_, 4);
lean_inc(v_errorMsg_642_);
if (lean_obj_tag(v_errorMsg_642_) == 0)
{
lean_object* v_stxStack_643_; lean_object* v_pos_644_; lean_object* v_pBack_645_; lean_object* v___y_647_; lean_object* v___y_651_; uint8_t v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; uint8_t v___y_669_; uint8_t v___x_682_; uint8_t v___x_683_; 
v_stxStack_643_ = lean_ctor_get(v_s_641_, 0);
lean_inc_ref(v_stxStack_643_);
v_pos_644_ = lean_ctor_get(v_s_641_, 2);
lean_inc(v_pos_644_);
v_pBack_645_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_643_);
lean_dec_ref(v_stxStack_643_);
v___x_682_ = 0;
v___x_683_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_636_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_684_ = l_Lean_Parser_ParserState_stackSize(v_s_641_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_iniSz_640_, v___x_685_);
v___x_687_ = lean_nat_dec_eq(v___x_684_, v___x_686_);
lean_dec(v___x_686_);
lean_dec(v___x_684_);
if (v___x_687_ == 0)
{
lean_dec(v_pBack_645_);
lean_dec(v_pos_644_);
lean_dec(v_iniSz_640_);
lean_dec(v_pos_639_);
lean_dec_ref(v_c_637_);
lean_dec_ref(v_q_635_);
return v_s_641_;
}
else
{
v___y_669_ = v___x_683_;
goto v___jp_668_;
}
}
else
{
v___y_669_ = v___x_683_;
goto v___jp_668_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = l_Lean_Parser_ParserState_restore(v___y_647_, v_iniSz_640_, v_pos_644_);
lean_dec(v_iniSz_640_);
v___x_649_ = l_Lean_Parser_ParserState_pushSyntax(v___x_648_, v_pBack_645_);
return v___x_649_;
}
v___jp_650_:
{
lean_object* v_stxStack_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_stxStack_652_ = lean_ctor_get(v___y_651_, 0);
v___x_653_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_652_);
lean_inc(v___x_653_);
v___x_654_ = l_Lean_Syntax_isAntiquots(v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v___x_653_);
v___y_647_ = v___y_651_;
goto v___jp_646_;
}
else
{
lean_object* v_s_655_; lean_object* v_s_656_; lean_object* v_s_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_pos_644_);
v_s_655_ = l_Lean_Parser_ParserState_popSyntax(v___y_651_);
v_s_656_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_645_, v_s_655_);
v_s_657_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_653_, v_s_656_);
v___x_658_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_659_ = l_Lean_Parser_ParserState_mkNode(v_s_657_, v___x_658_, v_iniSz_640_);
lean_dec(v_iniSz_640_);
return v___x_659_;
}
}
v___jp_660_:
{
if (v___y_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = l_Lean_Parser_ParserState_stackSize(v___y_662_);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_iniSz_640_, v___x_665_);
v___x_667_ = lean_nat_dec_eq(v___x_664_, v___x_666_);
lean_dec(v___x_666_);
lean_dec(v___x_664_);
if (v___x_667_ == 0)
{
if (v___y_661_ == 0)
{
v___y_651_ = v___y_662_;
goto v___jp_650_;
}
else
{
v___y_647_ = v___y_662_;
goto v___jp_646_;
}
}
else
{
v___y_651_ = v___y_662_;
goto v___jp_650_;
}
}
else
{
v___y_647_ = v___y_662_;
goto v___jp_646_;
}
}
v___jp_668_:
{
if (v___y_669_ == 0)
{
uint8_t v___x_670_; 
lean_inc(v_pBack_645_);
v___x_670_ = l_Lean_Syntax_isAntiquots(v_pBack_645_);
if (v___x_670_ == 0)
{
lean_dec(v_pBack_645_);
lean_dec(v_pos_644_);
lean_dec(v_iniSz_640_);
lean_dec(v_pos_639_);
lean_dec_ref(v_c_637_);
lean_dec_ref(v_q_635_);
return v_s_641_;
}
else
{
lean_object* v_s_671_; lean_object* v_s_672_; lean_object* v_pos_673_; lean_object* v_errorMsg_674_; uint8_t v___x_675_; 
v_s_671_ = l_Lean_Parser_ParserState_restore(v_s_641_, v_iniSz_640_, v_pos_639_);
v_s_672_ = lean_apply_2(v_q_635_, v_c_637_, v_s_671_);
v_pos_673_ = lean_ctor_get(v_s_672_, 2);
lean_inc(v_pos_673_);
v_errorMsg_674_ = lean_ctor_get(v_s_672_, 4);
lean_inc(v_errorMsg_674_);
v___x_675_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_674_, v_errorMsg_642_);
lean_dec(v_errorMsg_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_pos_673_);
v___x_676_ = l_Lean_Parser_ParserState_restore(v_s_672_, v_iniSz_640_, v_pos_644_);
lean_dec(v_iniSz_640_);
v___x_677_ = l_Lean_Parser_ParserState_pushSyntax(v___x_676_, v_pBack_645_);
return v___x_677_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_lt(v_pos_644_, v_pos_673_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_lt(v_pos_673_, v_pos_644_);
lean_dec(v_pos_673_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; uint8_t v___x_681_; 
v___x_680_ = 2;
v___x_681_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_636_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_661_ = v___x_675_;
v___y_662_ = v_s_672_;
v___y_663_ = v___x_675_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___x_675_;
v___y_662_ = v_s_672_;
v___y_663_ = v___x_679_;
goto v___jp_660_;
}
}
else
{
v___y_661_ = v___x_675_;
v___y_662_ = v_s_672_;
v___y_663_ = v___x_679_;
goto v___jp_660_;
}
}
else
{
lean_dec(v_pos_673_);
lean_dec(v_pBack_645_);
lean_dec(v_pos_644_);
lean_dec(v_iniSz_640_);
return v_s_672_;
}
}
}
}
else
{
lean_dec(v_pBack_645_);
lean_dec(v_pos_644_);
lean_dec(v_iniSz_640_);
lean_dec(v_pos_639_);
lean_dec_ref(v_c_637_);
lean_dec_ref(v_q_635_);
return v_s_641_;
}
}
}
else
{
lean_object* v_pos_688_; lean_object* v_val_689_; uint8_t v___x_690_; 
v_pos_688_ = lean_ctor_get(v_s_641_, 2);
lean_inc(v_pos_688_);
v_val_689_ = lean_ctor_get(v_errorMsg_642_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v_errorMsg_642_, 1);
v___x_690_ = lean_nat_dec_eq(v_pos_688_, v_pos_639_);
lean_dec(v_pos_688_);
if (v___x_690_ == 0)
{
lean_dec(v_val_689_);
lean_dec(v_iniSz_640_);
lean_dec(v_pos_639_);
lean_dec_ref(v_c_637_);
lean_dec_ref(v_q_635_);
return v_s_641_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_inc(v_pos_639_);
v___x_691_ = l_Lean_Parser_ParserState_restore(v_s_641_, v_iniSz_640_, v_pos_639_);
lean_dec(v_iniSz_640_);
v___x_692_ = lean_apply_2(v_q_635_, v_c_637_, v___x_691_);
v___x_693_ = l_Lean_Parser_mergeOrElseErrors(v___x_692_, v_val_689_, v_pos_639_, v___x_690_);
lean_dec(v_pos_639_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_694_, lean_object* v_q_695_, lean_object* v_antiquotBehavior_696_, lean_object* v_c_697_, lean_object* v_s_698_){
_start:
{
uint8_t v_antiquotBehavior_boxed_699_; lean_object* v_res_700_; 
v_antiquotBehavior_boxed_699_ = lean_unbox(v_antiquotBehavior_696_);
v_res_700_ = l_Lean_Parser_orelseFnCore(v_p_694_, v_q_695_, v_antiquotBehavior_boxed_699_, v_c_697_, v_s_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_701_, lean_object* v_q_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
uint8_t v___x_705_; lean_object* v___x_706_; 
v___x_705_ = 2;
v___x_706_ = l_Lean_Parser_orelseFnCore(v_p_701_, v_q_702_, v___x_705_, v_a_703_, v_a_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_707_, lean_object* v_q_708_){
_start:
{
lean_object* v_collectTokens_709_; lean_object* v_collectKinds_710_; lean_object* v_firstTokens_711_; lean_object* v_collectTokens_712_; lean_object* v_collectKinds_713_; lean_object* v_firstTokens_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
v_collectTokens_709_ = lean_ctor_get(v_p_707_, 0);
lean_inc_ref(v_collectTokens_709_);
v_collectKinds_710_ = lean_ctor_get(v_p_707_, 1);
lean_inc_ref(v_collectKinds_710_);
v_firstTokens_711_ = lean_ctor_get(v_p_707_, 2);
lean_inc(v_firstTokens_711_);
lean_dec_ref(v_p_707_);
v_collectTokens_712_ = lean_ctor_get(v_q_708_, 0);
v_collectKinds_713_ = lean_ctor_get(v_q_708_, 1);
v_firstTokens_714_ = lean_ctor_get(v_q_708_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_q_708_);
if (v_isSharedCheck_724_ == 0)
{
v___x_716_ = v_q_708_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_firstTokens_714_);
lean_inc(v_collectKinds_713_);
lean_inc(v_collectTokens_712_);
lean_dec(v_q_708_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_718_, 0, v_collectKinds_713_);
lean_closure_set(v___f_718_, 1, v_collectKinds_710_);
v___f_719_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_719_, 0, v_collectTokens_712_);
lean_closure_set(v___f_719_, 1, v_collectTokens_709_);
v___x_720_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_711_, v_firstTokens_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_720_);
lean_ctor_set(v___x_716_, 1, v___f_718_);
lean_ctor_set(v___x_716_, 0, v___f_719_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___f_719_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___f_718_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_725_, lean_object* v_p2_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = lean_apply_1(v_p2_726_, v___x_729_);
v___x_731_ = l_Lean_Parser_orelseFn(v_p1_725_, v___x_730_, v___y_727_, v___y_728_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_734_, lean_object* v_q_735_){
_start:
{
lean_object* v_info_736_; lean_object* v_fn_737_; lean_object* v_info_738_; lean_object* v_fn_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v_info_736_ = lean_ctor_get(v_p_734_, 0);
lean_inc_ref(v_info_736_);
v_fn_737_ = lean_ctor_get(v_p_734_, 1);
lean_inc_ref(v_fn_737_);
lean_dec_ref(v_p_734_);
v_info_738_ = lean_ctor_get(v_q_735_, 0);
v_fn_739_ = lean_ctor_get(v_q_735_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_q_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_741_ = v_q_735_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_fn_739_);
lean_inc(v_info_738_);
lean_dec(v_q_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = l_Lean_Parser_orelseInfo(v_info_736_, v_info_738_);
v___x_744_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_744_, 0, v_fn_737_);
lean_closure_set(v___x_744_, 1, v_fn_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_744_);
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_757_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_758_ = l_Lean_addBuiltinDocString(v___x_756_, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_761_, lean_object* v_b_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_apply_1(v_b_762_, v___x_763_);
v___x_765_ = l_Lean_Parser_orelse(v_a_761_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_768_){
_start:
{
lean_object* v_collectTokens_769_; lean_object* v_collectKinds_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
v_collectTokens_769_ = lean_ctor_get(v_info_768_, 0);
v_collectKinds_770_ = lean_ctor_get(v_info_768_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_info_768_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_info_768_, 2);
lean_dec(v_unused_779_);
v___x_772_ = v_info_768_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_collectKinds_770_);
lean_inc(v_collectTokens_769_);
lean_dec(v_info_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_box(1);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 2, v___x_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_collectTokens_769_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_collectKinds_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_780_, lean_object* v_c_781_, lean_object* v_s_782_){
_start:
{
lean_object* v_pos_783_; lean_object* v___x_784_; lean_object* v_errorMsg_785_; 
v_pos_783_ = lean_ctor_get(v_s_782_, 2);
lean_inc(v_pos_783_);
v___x_784_ = lean_apply_2(v_p_780_, v_c_781_, v_s_782_);
v_errorMsg_785_ = lean_ctor_get(v___x_784_, 4);
lean_inc(v_errorMsg_785_);
if (lean_obj_tag(v_errorMsg_785_) == 1)
{
lean_object* v_stxStack_786_; lean_object* v_lhsPrec_787_; lean_object* v_cache_788_; lean_object* v_recoveredErrors_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_stxStack_786_ = lean_ctor_get(v___x_784_, 0);
v_lhsPrec_787_ = lean_ctor_get(v___x_784_, 1);
v_cache_788_ = lean_ctor_get(v___x_784_, 3);
v_recoveredErrors_789_ = lean_ctor_get(v___x_784_, 5);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; 
v_unused_797_ = lean_ctor_get(v___x_784_, 4);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v___x_784_, 2);
lean_dec(v_unused_798_);
v___x_791_ = v___x_784_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_recoveredErrors_789_);
lean_inc(v_cache_788_);
lean_inc(v_lhsPrec_787_);
lean_inc(v_stxStack_786_);
lean_dec(v___x_784_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 2, v_pos_783_);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_stxStack_786_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_lhsPrec_787_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_pos_783_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_cache_788_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_errorMsg_785_);
lean_ctor_set(v_reuseFailAlloc_795_, 5, v_recoveredErrors_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_dec(v_errorMsg_785_);
lean_dec(v_pos_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_799_){
_start:
{
lean_object* v_info_800_; lean_object* v_fn_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_info_800_ = lean_ctor_get(v_p_799_, 0);
v_fn_801_ = lean_ctor_get(v_p_799_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_p_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v_p_799_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_fn_801_);
lean_inc(v_info_800_);
lean_dec(v_p_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_805_, 0, v_fn_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_info_800_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_818_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_819_ = l_Lean_addBuiltinDocString(v___x_817_, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_initialPos_824_; lean_object* v_initialSize_825_; lean_object* v_initialPos_826_; lean_object* v_initialSize_827_; uint8_t v___x_828_; 
v_initialPos_824_ = lean_ctor_get(v_x_822_, 0);
v_initialSize_825_ = lean_ctor_get(v_x_822_, 1);
v_initialPos_826_ = lean_ctor_get(v_x_823_, 0);
v_initialSize_827_ = lean_ctor_get(v_x_823_, 1);
v___x_828_ = lean_nat_dec_eq(v_initialPos_824_, v_initialPos_826_);
if (v___x_828_ == 0)
{
return v___x_828_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = lean_nat_dec_eq(v_initialSize_825_, v_initialSize_827_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_830_, v_x_831_);
lean_dec_ref(v_x_831_);
lean_dec_ref(v_x_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v_initialPos_838_; lean_object* v_initialSize_839_; lean_object* v_initialPos_840_; lean_object* v_initialSize_841_; uint8_t v___x_842_; 
v_initialPos_838_ = lean_ctor_get(v_x_836_, 0);
v_initialSize_839_ = lean_ctor_get(v_x_836_, 1);
v_initialPos_840_ = lean_ctor_get(v_x_837_, 0);
v_initialSize_841_ = lean_ctor_get(v_x_837_, 1);
v___x_842_ = lean_nat_dec_eq(v_initialPos_838_, v_initialPos_840_);
if (v___x_842_ == 0)
{
return v___x_842_;
}
else
{
uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_eq(v_initialSize_839_, v_initialSize_841_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_844_, v_x_845_);
lean_dec_ref(v_x_845_);
lean_dec_ref(v_x_844_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_851_, v_x_852_);
lean_dec_ref(v_x_852_);
lean_dec_ref(v_x_851_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_unsigned_to_nat(14u);
v___x_869_ = lean_nat_to_int(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_unsigned_to_nat(15u);
v___x_883_ = lean_nat_to_int(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_885_ = lean_string_length(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_887_ = lean_nat_to_int(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_890_){
_start:
{
lean_object* v_initialPos_891_; lean_object* v_initialSize_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_930_; 
v_initialPos_891_ = lean_ctor_get(v_x_890_, 0);
v_initialSize_892_ = lean_ctor_get(v_x_890_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_890_);
if (v_isSharedCheck_930_ == 0)
{
v___x_894_ = v_x_890_;
v_isShared_895_ = v_isSharedCheck_930_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_initialSize_892_);
lean_inc(v_initialPos_891_);
lean_dec(v_x_890_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_930_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_896_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_897_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_898_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_899_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_900_ = l_Nat_reprFast(v_initialPos_891_);
v___x_901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 5);
lean_ctor_set(v___x_894_, 1, v___x_901_);
lean_ctor_set(v___x_894_, 0, v___x_899_);
v___x_903_ = v___x_894_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_929_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_904_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_898_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = 0;
v___x_908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_897_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_box(1);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_896_);
v___x_917_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_918_ = l_Nat_reprFast(v_initialSize_892_);
v___x_919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
v___x_920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_917_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_907_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_916_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_924_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_922_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_904_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_923_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_907_);
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_931_, lean_object* v_prec_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_934_, lean_object* v_prec_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_934_, v_prec_935_);
lean_dec(v_prec_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_939_, lean_object* v_recover_940_, lean_object* v_c_941_, lean_object* v_s_942_){
_start:
{
lean_object* v_stxStack_943_; lean_object* v_pos_944_; lean_object* v_s_945_; lean_object* v_errorMsg_946_; 
v_stxStack_943_ = lean_ctor_get(v_s_942_, 0);
lean_inc_ref(v_stxStack_943_);
v_pos_944_ = lean_ctor_get(v_s_942_, 2);
lean_inc(v_pos_944_);
lean_inc_ref(v_c_941_);
v_s_945_ = lean_apply_2(v_p_939_, v_c_941_, v_s_942_);
v_errorMsg_946_ = lean_ctor_get(v_s_945_, 4);
lean_inc(v_errorMsg_946_);
if (lean_obj_tag(v_errorMsg_946_) == 1)
{
lean_object* v_stxStack_947_; lean_object* v_lhsPrec_948_; lean_object* v_pos_949_; lean_object* v_cache_950_; lean_object* v_recoveredErrors_951_; lean_object* v_val_952_; lean_object* v_iniSz_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_s_x27_957_; lean_object* v_stxStack_958_; lean_object* v_pos_959_; lean_object* v_errorMsg_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_971_; 
v_stxStack_947_ = lean_ctor_get(v_s_945_, 0);
lean_inc_ref(v_stxStack_947_);
v_lhsPrec_948_ = lean_ctor_get(v_s_945_, 1);
lean_inc_n(v_lhsPrec_948_, 2);
v_pos_949_ = lean_ctor_get(v_s_945_, 2);
lean_inc(v_pos_949_);
v_cache_950_ = lean_ctor_get(v_s_945_, 3);
lean_inc_ref_n(v_cache_950_, 2);
v_recoveredErrors_951_ = lean_ctor_get(v_s_945_, 5);
lean_inc_ref_n(v_recoveredErrors_951_, 2);
v_val_952_ = lean_ctor_get(v_errorMsg_946_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_errorMsg_946_, 1);
v_iniSz_953_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_943_);
lean_dec_ref(v_stxStack_943_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_pos_944_);
lean_ctor_set(v___x_954_, 1, v_iniSz_953_);
v___x_955_ = lean_box(0);
v___x_956_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_956_, 0, v_stxStack_947_);
lean_ctor_set(v___x_956_, 1, v_lhsPrec_948_);
lean_ctor_set(v___x_956_, 2, v_pos_949_);
lean_ctor_set(v___x_956_, 3, v_cache_950_);
lean_ctor_set(v___x_956_, 4, v___x_955_);
lean_ctor_set(v___x_956_, 5, v_recoveredErrors_951_);
v_s_x27_957_ = lean_apply_3(v_recover_940_, v___x_954_, v_c_941_, v___x_956_);
v_stxStack_958_ = lean_ctor_get(v_s_x27_957_, 0);
v_pos_959_ = lean_ctor_get(v_s_x27_957_, 2);
v_errorMsg_960_ = lean_ctor_get(v_s_x27_957_, 4);
v_isSharedCheck_971_ = !lean_is_exclusive(v_s_x27_957_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; 
v_unused_972_ = lean_ctor_get(v_s_x27_957_, 5);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_s_x27_957_, 3);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_s_x27_957_, 1);
lean_dec(v_unused_974_);
v___x_962_ = v_s_x27_957_;
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_errorMsg_960_);
lean_inc(v_pos_959_);
lean_inc(v_stxStack_958_);
lean_dec(v_s_x27_957_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
uint8_t v___x_964_; 
v___x_964_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_960_, v___x_955_);
lean_dec(v_errorMsg_960_);
if (v___x_964_ == 0)
{
lean_del_object(v___x_962_);
lean_dec(v_pos_959_);
lean_dec_ref(v_stxStack_958_);
lean_dec(v_val_952_);
lean_dec_ref(v_recoveredErrors_951_);
lean_dec_ref(v_cache_950_);
lean_dec(v_lhsPrec_948_);
return v_s_945_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
lean_dec_ref(v_s_945_);
lean_inc_ref(v_stxStack_958_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_stxStack_958_);
lean_ctor_set(v___x_965_, 1, v_val_952_);
lean_inc(v_pos_959_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_pos_959_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_array_push(v_recoveredErrors_951_, v___x_966_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 5, v___x_967_);
lean_ctor_set(v___x_962_, 4, v___x_955_);
lean_ctor_set(v___x_962_, 3, v_cache_950_);
lean_ctor_set(v___x_962_, 1, v_lhsPrec_948_);
v___x_969_ = v___x_962_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_stxStack_958_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_lhsPrec_948_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_pos_959_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_cache_950_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_dec(v_errorMsg_946_);
lean_dec(v_pos_944_);
lean_dec_ref(v_stxStack_943_);
lean_dec_ref(v_c_941_);
lean_dec_ref(v_recover_940_);
return v_s_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_975_, lean_object* v_s_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_979_; lean_object* v_fn_980_; lean_object* v___x_981_; 
v___x_979_ = lean_apply_1(v_handler_975_, v_s_976_);
v_fn_980_ = lean_ctor_get(v___x_979_, 1);
lean_inc_ref(v_fn_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_apply_2(v_fn_980_, v___y_977_, v___y_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_982_, lean_object* v_handler_983_){
_start:
{
lean_object* v_info_984_; lean_object* v_fn_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v_info_984_ = lean_ctor_get(v_parser_982_, 0);
v_fn_985_ = lean_ctor_get(v_parser_982_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_parser_982_);
if (v_isSharedCheck_994_ == 0)
{
v___x_987_ = v_parser_982_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_fn_985_);
lean_inc(v_info_984_);
lean_dec(v_parser_982_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_989_, 0, v_handler_983_);
v___x_990_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_990_, 0, v_fn_985_);
lean_closure_set(v___x_990_, 1, v___f_989_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_info_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_1003_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_1004_ = l_Lean_addBuiltinDocString(v___x_1002_, v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_1007_, lean_object* v_x_1008_){
_start:
{
lean_inc_ref(v_handler_1007_);
return v_handler_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Parser_recover___lam__0(v_handler_1009_, v_x_1010_);
lean_dec_ref(v_x_1010_);
lean_dec_ref(v_handler_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1012_, lean_object* v_handler_1013_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; 
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1014_, 0, v_handler_1013_);
v___x_1015_ = l_Lean_Parser_recover_x27(v_parser_1012_, v___f_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1024_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1025_ = l_Lean_addBuiltinDocString(v___x_1023_, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1031_, lean_object* v_c_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v_pos_1034_; lean_object* v_iniSz_1035_; lean_object* v___y_1037_; lean_object* v_s_1040_; lean_object* v_pos_1041_; lean_object* v_errorMsg_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_pos_1034_ = lean_ctor_get(v_s_1033_, 2);
lean_inc(v_pos_1034_);
v_iniSz_1035_ = l_Lean_Parser_ParserState_stackSize(v_s_1033_);
v_s_1040_ = lean_apply_2(v_p_1031_, v_c_1032_, v_s_1033_);
v_pos_1041_ = lean_ctor_get(v_s_1040_, 2);
lean_inc(v_pos_1041_);
v_errorMsg_1042_ = lean_ctor_get(v_s_1040_, 4);
lean_inc(v_errorMsg_1042_);
v___x_1043_ = lean_box(0);
v___x_1044_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1042_, v___x_1043_);
lean_dec(v_errorMsg_1042_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_nat_dec_eq(v_pos_1041_, v_pos_1034_);
lean_dec(v_pos_1041_);
if (v___x_1045_ == 0)
{
lean_dec(v_pos_1034_);
v___y_1037_ = v_s_1040_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Parser_ParserState_restore(v_s_1040_, v_iniSz_1035_, v_pos_1034_);
v___y_1037_ = v___x_1046_;
goto v___jp_1036_;
}
}
else
{
lean_dec(v_pos_1041_);
lean_dec(v_pos_1034_);
v___y_1037_ = v_s_1040_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1039_ = l_Lean_Parser_ParserState_mkNode(v___y_1037_, v___x_1038_, v_iniSz_1035_);
lean_dec(v_iniSz_1035_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1047_){
_start:
{
lean_object* v_collectTokens_1048_; lean_object* v_collectKinds_1049_; lean_object* v_firstTokens_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_collectTokens_1048_ = lean_ctor_get(v_p_1047_, 0);
v_collectKinds_1049_ = lean_ctor_get(v_p_1047_, 1);
v_firstTokens_1050_ = lean_ctor_get(v_p_1047_, 2);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_p_1047_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1052_ = v_p_1047_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_firstTokens_1050_);
lean_inc(v_collectKinds_1049_);
lean_inc(v_collectTokens_1048_);
lean_dec(v_p_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1054_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 2, v___x_1054_);
v___x_1056_ = v___x_1052_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_collectTokens_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_collectKinds_1049_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1059_){
_start:
{
lean_object* v_info_1060_; lean_object* v_fn_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
v_info_1060_ = lean_ctor_get(v_p_1059_, 0);
v_fn_1061_ = lean_ctor_get(v_p_1059_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_p_1059_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1063_ = v_p_1059_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_fn_1061_);
lean_inc(v_info_1060_);
lean_dec(v_p_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = l_Lean_Parser_optionalInfo(v_info_1060_);
v___x_1066_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1066_, 0, v_fn_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1066_);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1071_, lean_object* v_c_1072_, lean_object* v_s_1073_){
_start:
{
lean_object* v_pos_1074_; lean_object* v_iniSz_1075_; lean_object* v_s_1076_; lean_object* v_errorMsg_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_pos_1074_ = lean_ctor_get(v_s_1073_, 2);
lean_inc(v_pos_1074_);
v_iniSz_1075_ = l_Lean_Parser_ParserState_stackSize(v_s_1073_);
v_s_1076_ = lean_apply_2(v_p_1071_, v_c_1072_, v_s_1073_);
v_errorMsg_1077_ = lean_ctor_get(v_s_1076_, 4);
lean_inc(v_errorMsg_1077_);
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1077_, v___x_1078_);
lean_dec(v_errorMsg_1077_);
if (v___x_1079_ == 0)
{
lean_dec(v_iniSz_1075_);
lean_dec(v_pos_1074_);
return v_s_1076_;
}
else
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Parser_ParserState_restore(v_s_1076_, v_iniSz_1075_, v_pos_1074_);
lean_dec(v_iniSz_1075_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1081_){
_start:
{
lean_object* v_info_1082_; lean_object* v_fn_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_info_1082_ = lean_ctor_get(v_p_1081_, 0);
v_fn_1083_ = lean_ctor_get(v_p_1081_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_p_1081_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1085_ = v_p_1081_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_fn_1083_);
lean_inc(v_info_1082_);
lean_dec(v_p_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1087_, 0, v_fn_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_info_1082_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1100_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1101_ = l_Lean_addBuiltinDocString(v___x_1099_, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1105_, lean_object* v_msg_1106_, lean_object* v_c_1107_, lean_object* v_s_1108_){
_start:
{
lean_object* v_pos_1109_; lean_object* v_iniSz_1110_; lean_object* v_s_1111_; lean_object* v_errorMsg_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_pos_1109_ = lean_ctor_get(v_s_1108_, 2);
lean_inc(v_pos_1109_);
v_iniSz_1110_ = l_Lean_Parser_ParserState_stackSize(v_s_1108_);
v_s_1111_ = lean_apply_2(v_p_1105_, v_c_1107_, v_s_1108_);
v_errorMsg_1112_ = lean_ctor_get(v_s_1111_, 4);
lean_inc(v_errorMsg_1112_);
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1112_, v___x_1113_);
lean_dec(v_errorMsg_1112_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Parser_ParserState_restore(v_s_1111_, v_iniSz_1110_, v_pos_1109_);
lean_dec(v_iniSz_1110_);
return v___x_1115_;
}
else
{
lean_object* v_s_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_s_1116_ = l_Lean_Parser_ParserState_restore(v_s_1111_, v_iniSz_1110_, v_pos_1109_);
lean_dec(v_iniSz_1110_);
v___x_1117_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1118_ = lean_string_append(v___x_1117_, v_msg_1106_);
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1116_, v___x_1118_, v___x_1119_, v___x_1114_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1121_, lean_object* v_msg_1122_, lean_object* v_c_1123_, lean_object* v_s_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Parser_notFollowedByFn(v_p_1121_, v_msg_1122_, v_c_1123_, v_s_1124_);
lean_dec_ref(v_msg_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1126_, lean_object* v_msg_1127_){
_start:
{
lean_object* v_fn_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1137_; 
v_fn_1128_ = lean_ctor_get(v_p_1126_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_p_1126_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v_p_1126_, 0);
lean_dec(v_unused_1138_);
v___x_1130_ = v_p_1126_;
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_fn_1128_);
lean_dec(v_p_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1133_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1133_, 0, v_fn_1128_);
lean_closure_set(v___x_1133_, 1, v_msg_1127_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v___x_1133_);
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1147_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1148_ = l_Lean_addBuiltinDocString(v___x_1146_, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1152_, lean_object* v_c_1153_, lean_object* v_s_1154_){
_start:
{
lean_object* v_pos_1155_; lean_object* v_iniSz_1156_; lean_object* v_s_1157_; lean_object* v_pos_1158_; lean_object* v_errorMsg_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_pos_1155_ = lean_ctor_get(v_s_1154_, 2);
lean_inc(v_pos_1155_);
v_iniSz_1156_ = l_Lean_Parser_ParserState_stackSize(v_s_1154_);
lean_inc_ref(v_p_1152_);
lean_inc_ref(v_c_1153_);
v_s_1157_ = lean_apply_2(v_p_1152_, v_c_1153_, v_s_1154_);
v_pos_1158_ = lean_ctor_get(v_s_1157_, 2);
lean_inc(v_pos_1158_);
v_errorMsg_1159_ = lean_ctor_get(v_s_1157_, 4);
lean_inc(v_errorMsg_1159_);
v___x_1160_ = lean_box(0);
v___x_1161_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1159_, v___x_1160_);
lean_dec(v_errorMsg_1159_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
lean_dec_ref(v_c_1153_);
lean_dec_ref(v_p_1152_);
v___x_1162_ = lean_nat_dec_eq(v_pos_1155_, v_pos_1158_);
lean_dec(v_pos_1158_);
if (v___x_1162_ == 0)
{
lean_dec(v_iniSz_1156_);
lean_dec(v_pos_1155_);
return v_s_1157_;
}
else
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Parser_ParserState_restore(v_s_1157_, v_iniSz_1156_, v_pos_1155_);
lean_dec(v_iniSz_1156_);
return v___x_1163_;
}
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_nat_dec_eq(v_pos_1155_, v_pos_1158_);
lean_dec(v_pos_1158_);
lean_dec(v_pos_1155_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_add(v_iniSz_1156_, v___x_1165_);
v___x_1167_ = l_Lean_Parser_ParserState_stackSize(v_s_1157_);
v___x_1168_ = lean_nat_dec_lt(v___x_1166_, v___x_1167_);
lean_dec(v___x_1167_);
lean_dec(v___x_1166_);
if (v___x_1168_ == 0)
{
lean_dec(v_iniSz_1156_);
v_s_1154_ = v_s_1157_;
goto _start;
}
else
{
lean_object* v___x_1170_; lean_object* v_s_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1171_ = l_Lean_Parser_ParserState_mkNode(v_s_1157_, v___x_1170_, v_iniSz_1156_);
lean_dec(v_iniSz_1156_);
v_s_1154_ = v_s_1171_;
goto _start;
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec(v_iniSz_1156_);
lean_dec_ref(v_c_1153_);
lean_dec_ref(v_p_1152_);
v___x_1173_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1157_, v___x_1173_, v___x_1174_, v___x_1161_);
return v___x_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1176_, lean_object* v_c_1177_, lean_object* v_s_1178_){
_start:
{
lean_object* v_iniSz_1179_; lean_object* v_s_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_iniSz_1179_ = l_Lean_Parser_ParserState_stackSize(v_s_1178_);
v_s_1180_ = l_Lean_Parser_manyAux(v_p_1176_, v_c_1177_, v_s_1178_);
v___x_1181_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1182_ = l_Lean_Parser_ParserState_mkNode(v_s_1180_, v___x_1181_, v_iniSz_1179_);
lean_dec(v_iniSz_1179_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1183_){
_start:
{
lean_object* v_info_1184_; lean_object* v_fn_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1194_; 
v_info_1184_ = lean_ctor_get(v_p_1183_, 0);
v_fn_1185_ = lean_ctor_get(v_p_1183_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_p_1183_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1187_ = v_p_1183_;
v_isShared_1188_ = v_isSharedCheck_1194_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_fn_1185_);
lean_inc(v_info_1184_);
lean_dec(v_p_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1194_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1189_ = l_Lean_Parser_noFirstTokenInfo(v_info_1184_);
v___x_1190_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1190_, 0, v_fn_1185_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v___x_1190_);
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1195_, lean_object* v_c_1196_, lean_object* v_s_1197_){
_start:
{
lean_object* v_iniSz_1198_; lean_object* v___x_1199_; lean_object* v_s_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_iniSz_1198_ = l_Lean_Parser_ParserState_stackSize(v_s_1197_);
lean_inc_ref(v_p_1195_);
v___x_1199_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1199_, 0, v_p_1195_);
v_s_1200_ = l_Lean_Parser_andthenFn(v_p_1195_, v___x_1199_, v_c_1196_, v_s_1197_);
v___x_1201_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1202_ = l_Lean_Parser_ParserState_mkNode(v_s_1200_, v___x_1201_, v_iniSz_1198_);
lean_dec(v_iniSz_1198_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1203_){
_start:
{
lean_object* v_info_1204_; lean_object* v_fn_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_info_1204_ = lean_ctor_get(v_p_1203_, 0);
v_fn_1205_ = lean_ctor_get(v_p_1203_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_p_1203_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1207_ = v_p_1203_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_fn_1205_);
lean_inc(v_info_1204_);
lean_dec(v_p_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1209_, 0, v_fn_1205_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_info_1204_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1214_, lean_object* v_sep_1215_, uint8_t v_allowTrailingSep_1216_, lean_object* v_iniSz_1217_, uint8_t v_pOpt_1218_, lean_object* v_c_1219_, lean_object* v_s_1220_){
_start:
{
lean_object* v_s_1222_; lean_object* v_pos_1223_; lean_object* v_pos_1240_; lean_object* v_sz_1241_; lean_object* v_s_1242_; lean_object* v_pos_1243_; lean_object* v_errorMsg_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_pos_1240_ = lean_ctor_get(v_s_1220_, 2);
lean_inc(v_pos_1240_);
v_sz_1241_ = l_Lean_Parser_ParserState_stackSize(v_s_1220_);
lean_inc_ref(v_p_1214_);
lean_inc_ref(v_c_1219_);
v_s_1242_ = lean_apply_2(v_p_1214_, v_c_1219_, v_s_1220_);
v_pos_1243_ = lean_ctor_get(v_s_1242_, 2);
lean_inc(v_pos_1243_);
v_errorMsg_1244_ = lean_ctor_get(v_s_1242_, 4);
lean_inc(v_errorMsg_1244_);
v___x_1245_ = lean_box(0);
v___x_1246_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1244_, v___x_1245_);
lean_dec(v_errorMsg_1244_);
if (v___x_1246_ == 0)
{
uint8_t v___x_1247_; 
lean_dec_ref(v_c_1219_);
lean_dec_ref(v_sep_1215_);
lean_dec_ref(v_p_1214_);
v___x_1247_ = lean_nat_dec_lt(v_pos_1240_, v_pos_1243_);
lean_dec(v_pos_1243_);
if (v___x_1247_ == 0)
{
if (v_pOpt_1218_ == 0)
{
lean_object* v___x_1248_; lean_object* v_s_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_sz_1241_);
lean_dec(v_pos_1240_);
v___x_1248_ = lean_box(0);
v_s_1249_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1242_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1251_ = l_Lean_Parser_ParserState_mkNode(v_s_1249_, v___x_1250_, v_iniSz_1217_);
return v___x_1251_;
}
else
{
lean_object* v_s_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_s_1252_ = l_Lean_Parser_ParserState_restore(v_s_1242_, v_sz_1241_, v_pos_1240_);
lean_dec(v_sz_1241_);
v___x_1253_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1254_ = l_Lean_Parser_ParserState_mkNode(v_s_1252_, v___x_1253_, v_iniSz_1217_);
return v___x_1254_;
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_sz_1241_);
lean_dec(v_pos_1240_);
v___x_1255_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1256_ = l_Lean_Parser_ParserState_mkNode(v_s_1242_, v___x_1255_, v_iniSz_1217_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
lean_dec(v_pos_1240_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_sz_1241_, v___x_1257_);
v___x_1259_ = l_Lean_Parser_ParserState_stackSize(v_s_1242_);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
lean_dec(v___x_1259_);
lean_dec(v___x_1258_);
if (v___x_1260_ == 0)
{
lean_dec(v_sz_1241_);
v_s_1222_ = v_s_1242_;
v_pos_1223_ = v_pos_1243_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1261_; lean_object* v_s_1262_; lean_object* v_pos_1263_; 
lean_dec(v_pos_1243_);
v___x_1261_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1262_ = l_Lean_Parser_ParserState_mkNode(v_s_1242_, v___x_1261_, v_sz_1241_);
lean_dec(v_sz_1241_);
v_pos_1263_ = lean_ctor_get(v_s_1262_, 2);
lean_inc(v_pos_1263_);
v_s_1222_ = v_s_1262_;
v_pos_1223_ = v_pos_1263_;
goto v___jp_1221_;
}
}
v___jp_1221_:
{
lean_object* v_sz_1224_; lean_object* v_s_1225_; lean_object* v_errorMsg_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_sz_1224_ = l_Lean_Parser_ParserState_stackSize(v_s_1222_);
lean_inc_ref(v_sep_1215_);
lean_inc_ref(v_c_1219_);
v_s_1225_ = lean_apply_2(v_sep_1215_, v_c_1219_, v_s_1222_);
v_errorMsg_1226_ = lean_ctor_get(v_s_1225_, 4);
lean_inc(v_errorMsg_1226_);
v___x_1227_ = lean_box(0);
v___x_1228_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1226_, v___x_1227_);
lean_dec(v_errorMsg_1226_);
if (v___x_1228_ == 0)
{
lean_object* v_s_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v_c_1219_);
lean_dec_ref(v_sep_1215_);
lean_dec_ref(v_p_1214_);
v_s_1229_ = l_Lean_Parser_ParserState_restore(v_s_1225_, v_sz_1224_, v_pos_1223_);
lean_dec(v_sz_1224_);
v___x_1230_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1231_ = l_Lean_Parser_ParserState_mkNode(v_s_1229_, v___x_1230_, v_iniSz_1217_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
lean_dec(v_pos_1223_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_sz_1224_, v___x_1232_);
v___x_1234_ = l_Lean_Parser_ParserState_stackSize(v_s_1225_);
v___x_1235_ = lean_nat_dec_lt(v___x_1233_, v___x_1234_);
lean_dec(v___x_1234_);
lean_dec(v___x_1233_);
if (v___x_1235_ == 0)
{
lean_dec(v_sz_1224_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1216_;
lean_object* _tmp_6 = v_s_1225_;
v_pOpt_1218_ = _tmp_4;
v_s_1220_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1237_; lean_object* v_s_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1238_ = l_Lean_Parser_ParserState_mkNode(v_s_1225_, v___x_1237_, v_sz_1224_);
lean_dec(v_sz_1224_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1216_;
lean_object* _tmp_6 = v_s_1238_;
v_pOpt_1218_ = _tmp_4;
v_s_1220_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1264_, lean_object* v_sep_1265_, lean_object* v_allowTrailingSep_1266_, lean_object* v_iniSz_1267_, lean_object* v_pOpt_1268_, lean_object* v_c_1269_, lean_object* v_s_1270_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1271_; uint8_t v_pOpt_boxed_1272_; lean_object* v_res_1273_; 
v_allowTrailingSep_boxed_1271_ = lean_unbox(v_allowTrailingSep_1266_);
v_pOpt_boxed_1272_ = lean_unbox(v_pOpt_1268_);
v_res_1273_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1264_, v_sep_1265_, v_allowTrailingSep_boxed_1271_, v_iniSz_1267_, v_pOpt_boxed_1272_, v_c_1269_, v_s_1270_);
lean_dec(v_iniSz_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1274_, lean_object* v_sep_1275_, uint8_t v_allowTrailingSep_1276_, lean_object* v_iniSz_1277_, uint8_t v_pOpt_1278_, lean_object* v_c_1279_, lean_object* v_s_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1274_, v_sep_1275_, v_allowTrailingSep_1276_, v_iniSz_1277_, v_pOpt_1278_, v_c_1279_, v_s_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1282_, lean_object* v_sep_1283_, lean_object* v_allowTrailingSep_1284_, lean_object* v_iniSz_1285_, lean_object* v_pOpt_1286_, lean_object* v_c_1287_, lean_object* v_s_1288_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1289_; uint8_t v_pOpt_boxed_1290_; lean_object* v_res_1291_; 
v_allowTrailingSep_boxed_1289_ = lean_unbox(v_allowTrailingSep_1284_);
v_pOpt_boxed_1290_ = lean_unbox(v_pOpt_1286_);
v_res_1291_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1282_, v_sep_1283_, v_allowTrailingSep_boxed_1289_, v_iniSz_1285_, v_pOpt_boxed_1290_, v_c_1287_, v_s_1288_);
lean_dec(v_iniSz_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1292_, lean_object* v_p_1293_, lean_object* v_sep_1294_, lean_object* v_c_1295_, lean_object* v_s_1296_){
_start:
{
lean_object* v_iniSz_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; 
v_iniSz_1297_ = l_Lean_Parser_ParserState_stackSize(v_s_1296_);
v___x_1298_ = 1;
v___x_1299_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1293_, v_sep_1294_, v_allowTrailingSep_1292_, v_iniSz_1297_, v___x_1298_, v_c_1295_, v_s_1296_);
lean_dec(v_iniSz_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1300_, lean_object* v_p_1301_, lean_object* v_sep_1302_, lean_object* v_c_1303_, lean_object* v_s_1304_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1305_; lean_object* v_res_1306_; 
v_allowTrailingSep_boxed_1305_ = lean_unbox(v_allowTrailingSep_1300_);
v_res_1306_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1305_, v_p_1301_, v_sep_1302_, v_c_1303_, v_s_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1307_, lean_object* v_p_1308_, lean_object* v_sep_1309_, lean_object* v_c_1310_, lean_object* v_s_1311_){
_start:
{
lean_object* v_iniSz_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; 
v_iniSz_1312_ = l_Lean_Parser_ParserState_stackSize(v_s_1311_);
v___x_1313_ = 0;
v___x_1314_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1308_, v_sep_1309_, v_allowTrailingSep_1307_, v_iniSz_1312_, v___x_1313_, v_c_1310_, v_s_1311_);
lean_dec(v_iniSz_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1315_, lean_object* v_p_1316_, lean_object* v_sep_1317_, lean_object* v_c_1318_, lean_object* v_s_1319_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1320_; lean_object* v_res_1321_; 
v_allowTrailingSep_boxed_1320_ = lean_unbox(v_allowTrailingSep_1315_);
v_res_1321_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1320_, v_p_1316_, v_sep_1317_, v_c_1318_, v_s_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1322_, lean_object* v_sep_1323_){
_start:
{
lean_object* v_collectTokens_1324_; lean_object* v_collectKinds_1325_; lean_object* v_collectTokens_1326_; lean_object* v_collectKinds_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1337_; 
v_collectTokens_1324_ = lean_ctor_get(v_p_1322_, 0);
lean_inc_ref(v_collectTokens_1324_);
v_collectKinds_1325_ = lean_ctor_get(v_p_1322_, 1);
lean_inc_ref(v_collectKinds_1325_);
lean_dec_ref(v_p_1322_);
v_collectTokens_1326_ = lean_ctor_get(v_sep_1323_, 0);
v_collectKinds_1327_ = lean_ctor_get(v_sep_1323_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_sep_1323_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_sep_1323_, 2);
lean_dec(v_unused_1338_);
v___x_1329_ = v_sep_1323_;
v_isShared_1330_ = v_isSharedCheck_1337_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_collectKinds_1327_);
lean_inc(v_collectTokens_1326_);
lean_dec(v_sep_1323_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1337_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1331_, 0, v_collectKinds_1327_);
lean_closure_set(v___f_1331_, 1, v_collectKinds_1325_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1332_, 0, v_collectTokens_1326_);
lean_closure_set(v___f_1332_, 1, v_collectTokens_1324_);
v___x_1333_ = lean_box(1);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 2, v___x_1333_);
lean_ctor_set(v___x_1329_, 1, v___f_1331_);
lean_ctor_set(v___x_1329_, 0, v___f_1332_);
v___x_1335_ = v___x_1329_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___f_1332_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___f_1331_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1339_, lean_object* v_sep_1340_){
_start:
{
lean_object* v_collectTokens_1341_; lean_object* v_collectKinds_1342_; lean_object* v_firstTokens_1343_; lean_object* v_collectTokens_1344_; lean_object* v_collectKinds_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1354_; 
v_collectTokens_1341_ = lean_ctor_get(v_p_1339_, 0);
lean_inc_ref(v_collectTokens_1341_);
v_collectKinds_1342_ = lean_ctor_get(v_p_1339_, 1);
lean_inc_ref(v_collectKinds_1342_);
v_firstTokens_1343_ = lean_ctor_get(v_p_1339_, 2);
lean_inc(v_firstTokens_1343_);
lean_dec_ref(v_p_1339_);
v_collectTokens_1344_ = lean_ctor_get(v_sep_1340_, 0);
v_collectKinds_1345_ = lean_ctor_get(v_sep_1340_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_sep_1340_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_sep_1340_, 2);
lean_dec(v_unused_1355_);
v___x_1347_ = v_sep_1340_;
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_collectKinds_1345_);
lean_inc(v_collectTokens_1344_);
lean_dec(v_sep_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___f_1349_; lean_object* v___f_1350_; lean_object* v___x_1352_; 
v___f_1349_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1349_, 0, v_collectKinds_1345_);
lean_closure_set(v___f_1349_, 1, v_collectKinds_1342_);
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1350_, 0, v_collectTokens_1344_);
lean_closure_set(v___f_1350_, 1, v_collectTokens_1341_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 2, v_firstTokens_1343_);
lean_ctor_set(v___x_1347_, 1, v___f_1349_);
lean_ctor_set(v___x_1347_, 0, v___f_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___f_1350_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___f_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_firstTokens_1343_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1356_, lean_object* v_sep_1357_, uint8_t v_allowTrailingSep_1358_){
_start:
{
lean_object* v_info_1359_; lean_object* v_fn_1360_; lean_object* v_info_1361_; lean_object* v_fn_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1372_; 
v_info_1359_ = lean_ctor_get(v_p_1356_, 0);
lean_inc_ref(v_info_1359_);
v_fn_1360_ = lean_ctor_get(v_p_1356_, 1);
lean_inc_ref(v_fn_1360_);
lean_dec_ref(v_p_1356_);
v_info_1361_ = lean_ctor_get(v_sep_1357_, 0);
v_fn_1362_ = lean_ctor_get(v_sep_1357_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_sep_1357_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1364_ = v_sep_1357_;
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_fn_1362_);
lean_inc(v_info_1361_);
lean_dec(v_sep_1357_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1366_ = l_Lean_Parser_sepByInfo(v_info_1359_, v_info_1361_);
v___x_1367_ = lean_box(v_allowTrailingSep_1358_);
v___x_1368_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1368_, 0, v___x_1367_);
lean_closure_set(v___x_1368_, 1, v_fn_1360_);
lean_closure_set(v___x_1368_, 2, v_fn_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1368_);
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1370_ = v___x_1364_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1373_, lean_object* v_sep_1374_, lean_object* v_allowTrailingSep_1375_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1376_; lean_object* v_res_1377_; 
v_allowTrailingSep_boxed_1376_ = lean_unbox(v_allowTrailingSep_1375_);
v_res_1377_ = l_Lean_Parser_sepByNoAntiquot(v_p_1373_, v_sep_1374_, v_allowTrailingSep_boxed_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1378_, lean_object* v_sep_1379_, uint8_t v_allowTrailingSep_1380_){
_start:
{
lean_object* v_info_1381_; lean_object* v_fn_1382_; lean_object* v_info_1383_; lean_object* v_fn_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_info_1381_ = lean_ctor_get(v_p_1378_, 0);
lean_inc_ref(v_info_1381_);
v_fn_1382_ = lean_ctor_get(v_p_1378_, 1);
lean_inc_ref(v_fn_1382_);
lean_dec_ref(v_p_1378_);
v_info_1383_ = lean_ctor_get(v_sep_1379_, 0);
v_fn_1384_ = lean_ctor_get(v_sep_1379_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_sep_1379_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v_sep_1379_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_fn_1384_);
lean_inc(v_info_1383_);
lean_dec(v_sep_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1388_ = l_Lean_Parser_sepBy1Info(v_info_1381_, v_info_1383_);
v___x_1389_ = lean_box(v_allowTrailingSep_1380_);
v___x_1390_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1390_, 0, v___x_1389_);
lean_closure_set(v___x_1390_, 1, v_fn_1382_);
lean_closure_set(v___x_1390_, 2, v_fn_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1390_);
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1395_, lean_object* v_sep_1396_, lean_object* v_allowTrailingSep_1397_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1398_; lean_object* v_res_1399_; 
v_allowTrailingSep_boxed_1398_ = lean_unbox(v_allowTrailingSep_1397_);
v_res_1399_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1395_, v_sep_1396_, v_allowTrailingSep_boxed_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1400_, lean_object* v_f_1401_, lean_object* v_c_1402_, lean_object* v_s_1403_){
_start:
{
lean_object* v_s_1404_; lean_object* v_stxStack_1405_; lean_object* v_errorMsg_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_s_1404_ = lean_apply_2(v_p_1400_, v_c_1402_, v_s_1403_);
v_stxStack_1405_ = lean_ctor_get(v_s_1404_, 0);
lean_inc_ref(v_stxStack_1405_);
v_errorMsg_1406_ = lean_ctor_get(v_s_1404_, 4);
lean_inc(v_errorMsg_1406_);
v___x_1407_ = lean_box(0);
v___x_1408_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1406_, v___x_1407_);
lean_dec(v_errorMsg_1406_);
if (v___x_1408_ == 0)
{
lean_dec_ref(v_stxStack_1405_);
lean_dec_ref(v_f_1401_);
return v_s_1404_;
}
else
{
lean_object* v_stx_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_stx_1409_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1405_);
lean_dec_ref(v_stxStack_1405_);
v___x_1410_ = l_Lean_Parser_ParserState_popSyntax(v_s_1404_);
v___x_1411_ = lean_apply_1(v_f_1401_, v_stx_1409_);
v___x_1412_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1410_, v___x_1411_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1413_){
_start:
{
lean_object* v_collectTokens_1414_; lean_object* v_collectKinds_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_collectTokens_1414_ = lean_ctor_get(v_p_1413_, 0);
v_collectKinds_1415_ = lean_ctor_get(v_p_1413_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_p_1413_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_p_1413_, 2);
lean_dec(v_unused_1424_);
v___x_1417_ = v_p_1413_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_collectKinds_1415_);
lean_inc(v_collectTokens_1414_);
lean_dec(v_p_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_box(1);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 2, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_collectTokens_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_collectKinds_1415_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1425_, lean_object* v_f_1426_){
_start:
{
lean_object* v_info_1427_; lean_object* v_fn_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v_info_1427_ = lean_ctor_get(v_p_1425_, 0);
v_fn_1428_ = lean_ctor_get(v_p_1425_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_p_1425_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v_p_1425_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_fn_1428_);
lean_inc(v_info_1427_);
lean_dec(v_p_1425_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = l_Lean_Parser_withResultOfInfo(v_info_1427_);
v___x_1433_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1433_, 0, v_fn_1428_);
lean_closure_set(v___x_1433_, 1, v_f_1426_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1433_);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = l_Lean_Syntax_getNumArgs(v_stx_1438_);
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_dec_eq(v___x_1439_, v___x_1440_);
lean_dec(v___x_1439_);
if (v___x_1441_ == 0)
{
lean_inc(v_stx_1438_);
return v_stx_1438_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = l_Lean_Syntax_getArg(v_stx_1438_, v___x_1442_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1444_);
lean_dec(v_stx_1444_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1447_){
_start:
{
lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___f_1448_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1449_ = l_Lean_Parser_many1NoAntiquot(v_p_1447_);
v___x_1450_ = l_Lean_Parser_withResultOf(v___x_1449_, v___f_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1451_, lean_object* v_errorMsg_1452_, lean_object* v_c_1453_, lean_object* v_s_1454_){
_start:
{
lean_object* v_pos_1455_; lean_object* v_toInputContext_1456_; uint8_t v___x_1457_; 
v_pos_1455_ = lean_ctor_get(v_s_1454_, 2);
v_toInputContext_1456_ = lean_ctor_get(v_c_1453_, 0);
v___x_1457_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1456_, v_pos_1455_);
if (v___x_1457_ == 0)
{
lean_object* v_inputString_1458_; uint32_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_inputString_1458_ = lean_ctor_get(v_toInputContext_1456_, 0);
v___x_1459_ = lean_string_utf8_get_fast(v_inputString_1458_, v_pos_1455_);
v___x_1460_ = lean_box_uint32(v___x_1459_);
v___x_1461_ = lean_apply_1(v_p_1451_, v___x_1460_);
v___x_1462_ = lean_unbox(v___x_1461_);
if (v___x_1462_ == 0)
{
uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = 1;
v___x_1464_ = lean_box(0);
v___x_1465_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1454_, v_errorMsg_1452_, v___x_1464_, v___x_1463_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; 
lean_inc(v_pos_1455_);
lean_dec_ref(v_errorMsg_1452_);
v___x_1466_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1454_, v_c_1453_, v_pos_1455_);
lean_dec(v_pos_1455_);
return v___x_1466_;
}
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v_errorMsg_1452_);
lean_dec_ref(v_p_1451_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1454_, v___x_1467_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1469_, lean_object* v_errorMsg_1470_, lean_object* v_c_1471_, lean_object* v_s_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Parser_satisfyFn(v_p_1469_, v_errorMsg_1470_, v_c_1471_, v_s_1472_);
lean_dec_ref(v_c_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1474_, lean_object* v_c_1475_, lean_object* v_s_1476_){
_start:
{
lean_object* v_pos_1477_; lean_object* v_toInputContext_1478_; uint8_t v___x_1479_; 
v_pos_1477_ = lean_ctor_get(v_s_1476_, 2);
v_toInputContext_1478_ = lean_ctor_get(v_c_1475_, 0);
v___x_1479_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1478_, v_pos_1477_);
if (v___x_1479_ == 0)
{
lean_object* v_inputString_1480_; uint32_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_inputString_1480_ = lean_ctor_get(v_toInputContext_1478_, 0);
v___x_1481_ = lean_string_utf8_get_fast(v_inputString_1480_, v_pos_1477_);
v___x_1482_ = lean_box_uint32(v___x_1481_);
lean_inc_ref(v_p_1474_);
v___x_1483_ = lean_apply_1(v_p_1474_, v___x_1482_);
v___x_1484_ = lean_unbox(v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_inc(v_pos_1477_);
v___x_1485_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1476_, v_c_1475_, v_pos_1477_);
lean_dec(v_pos_1477_);
v_s_1476_ = v___x_1485_;
goto _start;
}
else
{
lean_dec_ref(v_p_1474_);
return v_s_1476_;
}
}
else
{
lean_dec_ref(v_p_1474_);
return v_s_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1487_, lean_object* v_c_1488_, lean_object* v_s_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Parser_takeUntilFn(v_p_1487_, v_c_1488_, v_s_1489_);
lean_dec_ref(v_c_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1491_, uint32_t v_c_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_box_uint32(v_c_1492_);
v___x_1494_ = lean_apply_1(v_p_1491_, v___x_1493_);
v___x_1495_ = lean_unbox(v___x_1494_);
if (v___x_1495_ == 0)
{
uint8_t v___x_1496_; 
v___x_1496_ = 1;
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1498_, lean_object* v_c_1499_){
_start:
{
uint32_t v_c_boxed_1500_; uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_c_boxed_1500_ = lean_unbox_uint32(v_c_1499_);
lean_dec(v_c_1499_);
v_res_1501_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1498_, v_c_boxed_1500_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v___f_1506_; lean_object* v___x_1507_; 
v___f_1506_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1506_, 0, v_p_1503_);
v___x_1507_ = l_Lean_Parser_takeUntilFn(v___f_1506_, v_a_1504_, v_a_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Parser_takeWhileFn(v_p_1508_, v_a_1509_, v_a_1510_);
lean_dec_ref(v_a_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1512_, lean_object* v_errorMsg_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_inc_ref(v_p_1512_);
v___x_1516_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1516_, 0, v_p_1512_);
lean_closure_set(v___x_1516_, 1, v_errorMsg_1513_);
v___x_1517_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1517_, 0, v_p_1512_);
v___x_1518_ = l_Lean_Parser_andthenFn(v___x_1516_, v___x_1517_, v_a_1514_, v_a_1515_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1520_, lean_object* v_s_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1523_ = lean_box(0);
v___x_1524_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1521_, v___x_1522_, v___x_1523_, v_pushMissingOnError_1520_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1525_, lean_object* v_s_1526_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1527_; lean_object* v_res_1528_; 
v_pushMissingOnError_boxed_1527_ = lean_unbox(v_pushMissingOnError_1525_);
v_res_1528_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1527_, v_s_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1529_, lean_object* v_nesting_1530_, lean_object* v_c_1531_, lean_object* v_s_1532_){
_start:
{
lean_object* v_pos_1533_; lean_object* v_toInputContext_1534_; uint8_t v___x_1535_; 
v_pos_1533_ = lean_ctor_get(v_s_1532_, 2);
v_toInputContext_1534_ = lean_ctor_get(v_c_1531_, 0);
v___x_1535_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1534_, v_pos_1533_);
if (v___x_1535_ == 0)
{
lean_object* v_inputString_1536_; uint32_t v_curr_1537_; lean_object* v_i_1538_; uint32_t v___x_1539_; uint8_t v___x_1540_; 
v_inputString_1536_ = lean_ctor_get(v_toInputContext_1534_, 0);
v_curr_1537_ = lean_string_utf8_get_fast(v_inputString_1536_, v_pos_1533_);
v_i_1538_ = lean_string_utf8_next_fast(v_inputString_1536_, v_pos_1533_);
v___x_1539_ = 45;
v___x_1540_ = lean_uint32_dec_eq(v_curr_1537_, v___x_1539_);
if (v___x_1540_ == 0)
{
uint32_t v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = 47;
v___x_1542_ = lean_uint32_dec_eq(v_curr_1537_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Parser_ParserState_setPos(v_s_1532_, v_i_1538_);
v_s_1532_ = v___x_1543_;
goto _start;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1534_, v_i_1538_);
if (v___x_1545_ == 0)
{
uint32_t v_curr_1546_; uint8_t v___x_1547_; 
v_curr_1546_ = lean_string_utf8_get_fast(v_inputString_1536_, v_i_1538_);
v___x_1547_ = lean_uint32_dec_eq(v_curr_1546_, v___x_1539_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Parser_ParserState_setPos(v_s_1532_, v_i_1538_);
v_s_1532_ = v___x_1548_;
goto _start;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_nesting_1530_, v___x_1550_);
lean_dec(v_nesting_1530_);
v___x_1552_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1532_, v_c_1531_, v_i_1538_);
v_nesting_1530_ = v___x_1551_;
v_s_1532_ = v___x_1552_;
goto _start;
}
}
else
{
lean_object* v___x_1554_; 
lean_dec(v_nesting_1530_);
v___x_1554_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1529_, v_s_1532_);
return v___x_1554_;
}
}
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1534_, v_i_1538_);
if (v___x_1555_ == 0)
{
uint32_t v_curr_1556_; uint32_t v___x_1557_; uint8_t v___x_1558_; 
v_curr_1556_ = lean_string_utf8_get_fast(v_inputString_1536_, v_i_1538_);
v___x_1557_ = 47;
v___x_1558_ = lean_uint32_dec_eq(v_curr_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Parser_ParserState_setPos(v_s_1532_, v_i_1538_);
v_s_1532_ = v___x_1559_;
goto _start;
}
else
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_nat_dec_eq(v_nesting_1530_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_nat_sub(v_nesting_1530_, v___x_1561_);
lean_dec(v_nesting_1530_);
v___x_1564_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1532_, v_c_1531_, v_i_1538_);
v_nesting_1530_ = v___x_1563_;
v_s_1532_ = v___x_1564_;
goto _start;
}
else
{
lean_object* v___x_1566_; 
lean_dec(v_nesting_1530_);
v___x_1566_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1532_, v_c_1531_, v_i_1538_);
return v___x_1566_;
}
}
}
else
{
lean_object* v___x_1567_; 
lean_dec(v_nesting_1530_);
v___x_1567_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1529_, v_s_1532_);
return v___x_1567_;
}
}
}
else
{
lean_object* v___x_1568_; 
lean_dec(v_nesting_1530_);
v___x_1568_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1529_, v_s_1532_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1569_, lean_object* v_nesting_1570_, lean_object* v_c_1571_, lean_object* v_s_1572_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1573_; lean_object* v_res_1574_; 
v_pushMissingOnError_boxed_1573_ = lean_unbox(v_pushMissingOnError_1569_);
v_res_1574_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1573_, v_nesting_1570_, v_c_1571_, v_s_1572_);
lean_dec_ref(v_c_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1575_){
_start:
{
uint32_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = 10;
v___x_1577_ = lean_uint32_dec_eq(v_c_1575_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1578_){
_start:
{
uint32_t v_c_boxed_1579_; uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_c_boxed_1579_ = lean_unbox_uint32(v_c_1578_);
lean_dec(v_c_1578_);
v_res_1580_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1579_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1587_, lean_object* v_s_1588_){
_start:
{
lean_object* v_pos_1589_; lean_object* v_toInputContext_1593_; uint8_t v___x_1594_; 
v_pos_1589_ = lean_ctor_get(v_s_1588_, 2);
v_toInputContext_1593_ = lean_ctor_get(v_c_1587_, 0);
v___x_1594_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1593_, v_pos_1589_);
if (v___x_1594_ == 0)
{
lean_object* v_inputString_1595_; uint32_t v_curr_1596_; uint32_t v___x_1597_; uint8_t v___x_1598_; 
v_inputString_1595_ = lean_ctor_get(v_toInputContext_1593_, 0);
v_curr_1596_ = lean_string_utf8_get_fast(v_inputString_1595_, v_pos_1589_);
v___x_1597_ = 9;
v___x_1598_ = lean_uint32_dec_eq(v_curr_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
uint32_t v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = 13;
v___x_1600_ = lean_uint32_dec_eq(v_curr_1596_, v___x_1599_);
if (v___x_1600_ == 0)
{
uint8_t v___y_1602_; uint8_t v___y_1629_; uint32_t v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = 32;
v___x_1633_ = lean_uint32_dec_eq(v_curr_1596_, v___x_1632_);
if (v___x_1633_ == 0)
{
v___y_1629_ = v___x_1598_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v___x_1633_;
goto v___jp_1628_;
}
v___jp_1601_:
{
if (v___y_1602_ == 0)
{
uint32_t v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = 45;
v___x_1604_ = lean_uint32_dec_eq(v_curr_1596_, v___x_1603_);
if (v___x_1604_ == 0)
{
uint32_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = 47;
v___x_1606_ = lean_uint32_dec_eq(v_curr_1596_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_dec_ref(v_c_1587_);
return v_s_1588_;
}
else
{
lean_object* v_i_1607_; uint32_t v_curr_1608_; uint8_t v___x_1609_; 
v_i_1607_ = lean_string_utf8_next_fast(v_inputString_1595_, v_pos_1589_);
v_curr_1608_ = lean_string_utf8_get(v_inputString_1595_, v_i_1607_);
v___x_1609_ = lean_uint32_dec_eq(v_curr_1608_, v___x_1603_);
if (v___x_1609_ == 0)
{
lean_dec_ref(v_c_1587_);
return v_s_1588_;
}
else
{
lean_object* v_i_1610_; uint32_t v_curr_1611_; uint8_t v___x_1612_; 
v_i_1610_ = lean_string_utf8_next(v_inputString_1595_, v_i_1607_);
v_curr_1611_ = lean_string_utf8_get(v_inputString_1595_, v_i_1610_);
v___x_1612_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1603_);
if (v___x_1612_ == 0)
{
uint32_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = 33;
v___x_1614_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_box(v___x_1614_);
v___x_1617_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1617_, 0, v___x_1616_);
lean_closure_set(v___x_1617_, 1, v___x_1615_);
v___x_1618_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1619_ = l_Lean_Parser_ParserState_next(v_s_1588_, v_c_1587_, v_i_1610_);
lean_dec(v_i_1610_);
v___x_1620_ = l_Lean_Parser_andthenFn(v___x_1617_, v___x_1618_, v_c_1587_, v___x_1619_);
return v___x_1620_;
}
else
{
lean_dec(v_i_1610_);
lean_dec_ref(v_c_1587_);
return v_s_1588_;
}
}
else
{
lean_dec(v_i_1610_);
lean_dec_ref(v_c_1587_);
return v_s_1588_;
}
}
}
}
else
{
lean_object* v_i_1621_; uint32_t v_curr_1622_; uint8_t v___x_1623_; 
v_i_1621_ = lean_string_utf8_next_fast(v_inputString_1595_, v_pos_1589_);
v_curr_1622_ = lean_string_utf8_get(v_inputString_1595_, v_i_1621_);
v___x_1623_ = lean_uint32_dec_eq(v_curr_1622_, v___x_1603_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v_c_1587_);
return v_s_1588_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1625_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1626_ = l_Lean_Parser_ParserState_next(v_s_1588_, v_c_1587_, v_i_1621_);
v___x_1627_ = l_Lean_Parser_andthenFn(v___x_1624_, v___x_1625_, v_c_1587_, v___x_1626_);
return v___x_1627_;
}
}
}
else
{
lean_inc(v_pos_1589_);
goto v___jp_1590_;
}
}
v___jp_1628_:
{
if (v___y_1629_ == 0)
{
if (v___x_1600_ == 0)
{
uint32_t v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = 10;
v___x_1631_ = lean_uint32_dec_eq(v_curr_1596_, v___x_1630_);
v___y_1602_ = v___x_1631_;
goto v___jp_1601_;
}
else
{
v___y_1602_ = v___x_1600_;
goto v___jp_1601_;
}
}
else
{
lean_inc(v_pos_1589_);
goto v___jp_1590_;
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_c_1587_);
v___x_1634_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1635_ = lean_box(0);
v___x_1636_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1588_, v___x_1634_, v___x_1635_, v___x_1598_);
return v___x_1636_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_c_1587_);
v___x_1637_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1638_ = lean_box(0);
v___x_1639_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1588_, v___x_1637_, v___x_1638_, v___x_1594_);
return v___x_1639_;
}
}
else
{
lean_dec_ref(v_c_1587_);
return v_s_1588_;
}
v___jp_1590_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1588_, v_c_1587_, v_pos_1589_);
lean_dec(v_pos_1589_);
v_s_1588_ = v___x_1591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1640_, lean_object* v_p_1641_){
_start:
{
lean_object* v_toInputContext_1642_; lean_object* v_inputString_1643_; lean_object* v_endPos_1644_; uint8_t v___x_1645_; 
v_toInputContext_1642_ = lean_ctor_get(v_c_1640_, 0);
v_inputString_1643_ = lean_ctor_get(v_toInputContext_1642_, 0);
v_endPos_1644_ = lean_ctor_get(v_toInputContext_1642_, 3);
v___x_1645_ = lean_nat_dec_le(v_p_1641_, v_endPos_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_inc(v_endPos_1644_);
lean_inc_ref(v_inputString_1643_);
v___x_1646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1646_, 0, v_inputString_1643_);
lean_ctor_set(v___x_1646_, 1, v_p_1641_);
lean_ctor_set(v___x_1646_, 2, v_endPos_1644_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; 
lean_inc(v_p_1641_);
lean_inc_ref(v_inputString_1643_);
v___x_1647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1647_, 0, v_inputString_1643_);
lean_ctor_set(v___x_1647_, 1, v_p_1641_);
lean_ctor_set(v___x_1647_, 2, v_p_1641_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1648_, lean_object* v_p_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1648_, v_p_1649_);
lean_dec_ref(v_c_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1651_, uint8_t v_trailingWs_1652_, lean_object* v_c_1653_, lean_object* v_s_1654_){
_start:
{
lean_object* v_toInputContext_1655_; lean_object* v_pos_1656_; lean_object* v_inputString_1657_; lean_object* v_endPos_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1686_; 
v_toInputContext_1655_ = lean_ctor_get(v_c_1653_, 0);
lean_inc_ref(v_toInputContext_1655_);
v_pos_1656_ = lean_ctor_get(v_s_1654_, 2);
v_inputString_1657_ = lean_ctor_get(v_toInputContext_1655_, 0);
v_endPos_1658_ = lean_ctor_get(v_toInputContext_1655_, 3);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_toInputContext_1655_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1687_ = lean_ctor_get(v_toInputContext_1655_, 2);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_toInputContext_1655_, 1);
lean_dec(v_unused_1688_);
v___x_1660_ = v_toInputContext_1655_;
v_isShared_1661_ = v_isSharedCheck_1686_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_endPos_1658_);
lean_inc(v_inputString_1657_);
lean_dec(v_toInputContext_1655_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1686_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_leading_1662_; lean_object* v_val_1663_; 
lean_inc(v_startPos_1651_);
v_leading_1662_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1653_, v_startPos_1651_);
v_val_1663_ = lean_string_utf8_extract(v_inputString_1657_, v_startPos_1651_, v_pos_1656_);
if (v_trailingWs_1652_ == 0)
{
lean_object* v_trailing_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec(v_endPos_1658_);
lean_dec_ref(v_inputString_1657_);
lean_inc(v_pos_1656_);
v_trailing_1664_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1653_, v_pos_1656_);
lean_dec_ref(v_c_1653_);
v___x_1665_ = lean_string_utf8_byte_size(v_val_1663_);
v___x_1666_ = lean_nat_add(v_startPos_1651_, v___x_1665_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 3, v___x_1666_);
lean_ctor_set(v___x_1660_, 2, v_trailing_1664_);
lean_ctor_set(v___x_1660_, 1, v_startPos_1651_);
lean_ctor_set(v___x_1660_, 0, v_leading_1662_);
v___x_1668_ = v___x_1660_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_leading_1662_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_startPos_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_trailing_1664_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v_atom_1669_; lean_object* v___x_1670_; 
v_atom_1669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1669_, 0, v___x_1668_);
lean_ctor_set(v_atom_1669_, 1, v_val_1663_);
v___x_1670_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1654_, v_atom_1669_);
return v___x_1670_;
}
}
else
{
lean_object* v_s_1672_; lean_object* v___y_1674_; lean_object* v_pos_1682_; uint8_t v___x_1683_; 
lean_inc(v_pos_1656_);
v_s_1672_ = l_Lean_Parser_whitespace(v_c_1653_, v_s_1654_);
v_pos_1682_ = lean_ctor_get(v_s_1672_, 2);
lean_inc(v_pos_1682_);
v___x_1683_ = lean_nat_dec_le(v_pos_1682_, v_endPos_1658_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec(v_pos_1682_);
v___x_1684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1684_, 0, v_inputString_1657_);
lean_ctor_set(v___x_1684_, 1, v_pos_1656_);
lean_ctor_set(v___x_1684_, 2, v_endPos_1658_);
v___y_1674_ = v___x_1684_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1685_; 
lean_dec(v_endPos_1658_);
v___x_1685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1685_, 0, v_inputString_1657_);
lean_ctor_set(v___x_1685_, 1, v_pos_1656_);
lean_ctor_set(v___x_1685_, 2, v_pos_1682_);
v___y_1674_ = v___x_1685_;
goto v___jp_1673_;
}
v___jp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = lean_string_utf8_byte_size(v_val_1663_);
v___x_1676_ = lean_nat_add(v_startPos_1651_, v___x_1675_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 3, v___x_1676_);
lean_ctor_set(v___x_1660_, 2, v___y_1674_);
lean_ctor_set(v___x_1660_, 1, v_startPos_1651_);
lean_ctor_set(v___x_1660_, 0, v_leading_1662_);
v___x_1678_ = v___x_1660_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_leading_1662_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_startPos_1651_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v___y_1674_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v_atom_1679_; lean_object* v___x_1680_; 
v_atom_1679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1679_, 0, v___x_1678_);
lean_ctor_set(v_atom_1679_, 1, v_val_1663_);
v___x_1680_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1672_, v_atom_1679_);
return v___x_1680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1689_, lean_object* v_trailingWs_1690_, lean_object* v_c_1691_, lean_object* v_s_1692_){
_start:
{
uint8_t v_trailingWs_boxed_1693_; lean_object* v_res_1694_; 
v_trailingWs_boxed_1693_ = lean_unbox(v_trailingWs_1690_);
v_res_1694_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1689_, v_trailingWs_boxed_1693_, v_c_1691_, v_s_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1695_, uint8_t v_trailingWs_1696_, lean_object* v_c_1697_, lean_object* v_s_1698_){
_start:
{
lean_object* v_pos_1699_; lean_object* v_s_1700_; lean_object* v_errorMsg_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_pos_1699_ = lean_ctor_get(v_s_1698_, 2);
lean_inc(v_pos_1699_);
lean_inc_ref(v_c_1697_);
v_s_1700_ = lean_apply_2(v_p_1695_, v_c_1697_, v_s_1698_);
v_errorMsg_1701_ = lean_ctor_get(v_s_1700_, 4);
lean_inc(v_errorMsg_1701_);
v___x_1702_ = lean_box(0);
v___x_1703_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1701_, v___x_1702_);
lean_dec(v_errorMsg_1701_);
if (v___x_1703_ == 0)
{
lean_dec(v_pos_1699_);
lean_dec_ref(v_c_1697_);
return v_s_1700_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1699_, v_trailingWs_1696_, v_c_1697_, v_s_1700_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1705_, lean_object* v_trailingWs_1706_, lean_object* v_c_1707_, lean_object* v_s_1708_){
_start:
{
uint8_t v_trailingWs_boxed_1709_; lean_object* v_res_1710_; 
v_trailingWs_boxed_1709_ = lean_unbox(v_trailingWs_1706_);
v_res_1710_ = l_Lean_Parser_rawFn(v_p_1705_, v_trailingWs_boxed_1709_, v_c_1707_, v_s_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1711_, uint32_t v_d_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_uint32_dec_eq(v_c_1711_, v_d_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1714_, lean_object* v_d_1715_){
_start:
{
uint32_t v_c_boxed_1716_; uint32_t v_d_boxed_1717_; uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_c_boxed_1716_ = lean_unbox_uint32(v_c_1714_);
lean_dec(v_c_1714_);
v_d_boxed_1717_ = lean_unbox_uint32(v_d_1715_);
lean_dec(v_d_1715_);
v_res_1718_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1716_, v_d_boxed_1717_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1722_, uint8_t v_trailingWs_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1726_ = lean_box_uint32(v_c_1722_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1727_, 0, v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1729_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1730_ = lean_string_push(v___x_1729_, v_c_1722_);
v___x_1731_ = lean_string_append(v___x_1728_, v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = lean_string_append(v___x_1731_, v___x_1728_);
v___x_1733_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1733_, 0, v___f_1727_);
lean_closure_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_Parser_rawFn(v___x_1733_, v_trailingWs_1723_, v_a_1724_, v_a_1725_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1735_, lean_object* v_trailingWs_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
uint32_t v_c_boxed_1739_; uint8_t v_trailingWs_boxed_1740_; lean_object* v_res_1741_; 
v_c_boxed_1739_ = lean_unbox_uint32(v_c_1735_);
lean_dec(v_c_1735_);
v_trailingWs_boxed_1740_ = lean_unbox(v_trailingWs_1736_);
v_res_1741_ = l_Lean_Parser_chFn(v_c_boxed_1739_, v_trailingWs_boxed_1740_, v_a_1737_, v_a_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1742_, uint8_t v_trailingWs_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1744_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1745_ = lean_box_uint32(v_c_1742_);
v___x_1746_ = lean_box(v_trailingWs_1743_);
v___x_1747_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1747_, 0, v___x_1745_);
lean_closure_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1744_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1749_, lean_object* v_trailingWs_1750_){
_start:
{
uint32_t v_c_boxed_1751_; uint8_t v_trailingWs_boxed_1752_; lean_object* v_res_1753_; 
v_c_boxed_1751_ = lean_unbox_uint32(v_c_1749_);
lean_dec(v_c_1749_);
v_trailingWs_boxed_1752_ = lean_unbox(v_trailingWs_1750_);
v_res_1753_ = l_Lean_Parser_rawCh(v_c_boxed_1751_, v_trailingWs_boxed_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1755_, lean_object* v_s_1756_){
_start:
{
lean_object* v_pos_1757_; lean_object* v_toInputContext_1758_; uint8_t v___x_1759_; 
v_pos_1757_ = lean_ctor_get(v_s_1756_, 2);
v_toInputContext_1758_ = lean_ctor_get(v_c_1755_, 0);
v___x_1759_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1758_, v_pos_1757_);
if (v___x_1759_ == 0)
{
lean_object* v_inputString_1760_; uint8_t v___x_1761_; uint32_t v_curr_1762_; lean_object* v_i_1763_; uint8_t v___y_1765_; uint8_t v___y_1771_; uint8_t v___y_1778_; uint32_t v___x_1784_; uint8_t v___x_1785_; 
v_inputString_1760_ = lean_ctor_get(v_toInputContext_1758_, 0);
v___x_1761_ = 1;
v_curr_1762_ = lean_string_utf8_get_fast(v_inputString_1760_, v_pos_1757_);
v_i_1763_ = lean_string_utf8_next_fast(v_inputString_1760_, v_pos_1757_);
v___x_1784_ = 48;
v___x_1785_ = lean_uint32_dec_le(v___x_1784_, v_curr_1762_);
if (v___x_1785_ == 0)
{
v___y_1778_ = v___x_1785_;
goto v___jp_1777_;
}
else
{
uint32_t v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = 57;
v___x_1787_ = lean_uint32_dec_le(v_curr_1762_, v___x_1786_);
v___y_1778_ = v___x_1787_;
goto v___jp_1777_;
}
v___jp_1764_:
{
if (v___y_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1767_ = lean_box(0);
v___x_1768_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1756_, v___x_1766_, v___x_1767_, v___x_1761_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Parser_ParserState_setPos(v_s_1756_, v_i_1763_);
return v___x_1769_;
}
}
v___jp_1770_:
{
if (v___y_1771_ == 0)
{
uint32_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = 65;
v___x_1773_ = lean_uint32_dec_le(v___x_1772_, v_curr_1762_);
if (v___x_1773_ == 0)
{
v___y_1765_ = v___x_1773_;
goto v___jp_1764_;
}
else
{
uint32_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = 70;
v___x_1775_ = lean_uint32_dec_le(v_curr_1762_, v___x_1774_);
v___y_1765_ = v___x_1775_;
goto v___jp_1764_;
}
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Parser_ParserState_setPos(v_s_1756_, v_i_1763_);
return v___x_1776_;
}
}
v___jp_1777_:
{
if (v___y_1778_ == 0)
{
uint32_t v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = 97;
v___x_1780_ = lean_uint32_dec_le(v___x_1779_, v_curr_1762_);
if (v___x_1780_ == 0)
{
v___y_1771_ = v___x_1780_;
goto v___jp_1770_;
}
else
{
uint32_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 102;
v___x_1782_ = lean_uint32_dec_le(v_curr_1762_, v___x_1781_);
v___y_1771_ = v___x_1782_;
goto v___jp_1770_;
}
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Parser_ParserState_setPos(v_s_1756_, v_i_1763_);
return v___x_1783_;
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_box(0);
v___x_1789_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1756_, v___x_1788_);
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
lean_object* v_inputString_1804_; uint8_t v___x_1805_; uint8_t v___y_1807_; uint32_t v_curr_1811_; uint8_t v___y_1813_; uint32_t v___x_1818_; uint8_t v___x_1819_; 
v_inputString_1804_ = lean_ctor_get(v_toInputContext_1802_, 0);
v___x_1805_ = 1;
v_curr_1811_ = lean_string_utf8_get_fast(v_inputString_1804_, v_pos_1798_);
v___x_1818_ = 10;
v___x_1819_ = lean_uint32_dec_eq(v_curr_1811_, v___x_1818_);
if (v___x_1819_ == 0)
{
uint32_t v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = 32;
v___x_1821_ = lean_uint32_dec_eq(v_curr_1811_, v___x_1820_);
if (v___x_1821_ == 0)
{
uint32_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = 9;
v___x_1823_ = lean_uint32_dec_eq(v_curr_1811_, v___x_1822_);
v___y_1813_ = v___x_1823_;
goto v___jp_1812_;
}
else
{
v___y_1813_ = v___x_1821_;
goto v___jp_1812_;
}
}
else
{
if (v_seenNewline_1795_ == 0)
{
lean_object* v___x_1824_; 
lean_inc(v_pos_1798_);
v___x_1824_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1797_, v_c_1796_, v_pos_1798_);
lean_dec(v_pos_1798_);
v_seenNewline_1795_ = v___x_1805_;
v_s_1797_ = v___x_1824_;
goto _start;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1827_ = lean_box(0);
v___x_1828_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1797_, v___x_1826_, v___x_1827_, v___x_1805_);
return v___x_1828_;
}
}
v___jp_1806_:
{
if (v___y_1807_ == 0)
{
if (v_seenNewline_1795_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1809_ = lean_box(0);
v___x_1810_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1797_, v___x_1808_, v___x_1809_, v___x_1805_);
return v___x_1810_;
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
v___jp_1812_:
{
if (v___y_1813_ == 0)
{
uint32_t v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = 13;
v___x_1815_ = lean_uint32_dec_eq(v_curr_1811_, v___x_1814_);
if (v___x_1815_ == 0)
{
uint32_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = 10;
v___x_1817_ = lean_uint32_dec_eq(v_curr_1811_, v___x_1816_);
v___y_1807_ = v___x_1817_;
goto v___jp_1806_;
}
else
{
v___y_1807_ = v___x_1815_;
goto v___jp_1806_;
}
}
else
{
lean_inc(v_pos_1798_);
goto v___jp_1799_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1829_, lean_object* v_c_1830_, lean_object* v_s_1831_){
_start:
{
uint8_t v_seenNewline_boxed_1832_; lean_object* v_res_1833_; 
v_seenNewline_boxed_1832_ = lean_unbox(v_seenNewline_1829_);
v_res_1833_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1832_, v_c_1830_, v_s_1831_);
lean_dec_ref(v_c_1830_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1835_);
v___x_1836_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1836_, 0, v___x_1835_);
lean_closure_set(v___x_1836_, 1, v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1838_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1839_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1839_, 0, v___x_1838_);
lean_closure_set(v___x_1839_, 1, v___x_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1840_, uint8_t v_inString_1841_, lean_object* v_c_1842_, lean_object* v_s_1843_){
_start:
{
lean_object* v_pos_1844_; lean_object* v_toInputContext_1845_; uint8_t v___x_1846_; 
v_pos_1844_ = lean_ctor_get(v_s_1843_, 2);
v_toInputContext_1845_ = lean_ctor_get(v_c_1842_, 0);
v___x_1846_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1845_, v_pos_1844_);
if (v___x_1846_ == 0)
{
lean_object* v_inputString_1847_; uint32_t v_curr_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_inputString_1847_ = lean_ctor_get(v_toInputContext_1845_, 0);
v_curr_1848_ = lean_string_utf8_get_fast(v_inputString_1847_, v_pos_1844_);
v___x_1849_ = lean_box_uint32(v_curr_1848_);
v___x_1850_ = lean_apply_1(v_isQuotable_1840_, v___x_1849_);
v___x_1851_ = lean_unbox(v___x_1850_);
if (v___x_1851_ == 0)
{
uint32_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = 120;
v___x_1853_ = lean_uint32_dec_eq(v_curr_1848_, v___x_1852_);
if (v___x_1853_ == 0)
{
uint32_t v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = 117;
v___x_1855_ = lean_uint32_dec_eq(v_curr_1848_, v___x_1854_);
if (v___x_1855_ == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = 1;
if (v_inString_1841_ == 0)
{
lean_dec_ref(v_c_1842_);
goto v___jp_1857_;
}
else
{
uint32_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = 10;
v___x_1862_ = lean_uint32_dec_eq(v_curr_1848_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v_c_1842_);
goto v___jp_1857_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Parser_stringGapFn(v___x_1855_, v_c_1842_, v_s_1843_);
lean_dec_ref(v_c_1842_);
return v___x_1863_;
}
}
v___jp_1857_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1859_ = lean_box(0);
v___x_1860_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1843_, v___x_1858_, v___x_1859_, v___x_1856_);
return v___x_1860_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_inc(v_pos_1844_);
v___x_1864_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1865_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1866_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1843_, v_c_1842_, v_pos_1844_);
lean_dec(v_pos_1844_);
v___x_1867_ = l_Lean_Parser_andthenFn(v___x_1864_, v___x_1865_, v_c_1842_, v___x_1866_);
return v___x_1867_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_inc(v_pos_1844_);
v___x_1868_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1869_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1843_, v_c_1842_, v_pos_1844_);
lean_dec(v_pos_1844_);
lean_inc_ref(v___x_1868_);
v___x_1870_ = l_Lean_Parser_andthenFn(v___x_1868_, v___x_1868_, v_c_1842_, v___x_1869_);
return v___x_1870_;
}
}
else
{
lean_object* v___x_1871_; 
lean_inc(v_pos_1844_);
v___x_1871_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1843_, v_c_1842_, v_pos_1844_);
lean_dec(v_pos_1844_);
lean_dec_ref(v_c_1842_);
return v___x_1871_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec_ref(v_c_1842_);
lean_dec_ref(v_isQuotable_1840_);
v___x_1872_ = lean_box(0);
v___x_1873_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1843_, v___x_1872_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1874_, lean_object* v_inString_1875_, lean_object* v_c_1876_, lean_object* v_s_1877_){
_start:
{
uint8_t v_inString_boxed_1878_; lean_object* v_res_1879_; 
v_inString_boxed_1878_ = lean_unbox(v_inString_1875_);
v_res_1879_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1874_, v_inString_boxed_1878_, v_c_1876_, v_s_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1880_){
_start:
{
uint8_t v___y_1882_; uint32_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = 92;
v___x_1892_ = lean_uint32_dec_eq(v_c_1880_, v___x_1891_);
if (v___x_1892_ == 0)
{
uint32_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = 34;
v___x_1894_ = lean_uint32_dec_eq(v_c_1880_, v___x_1893_);
v___y_1882_ = v___x_1894_;
goto v___jp_1881_;
}
else
{
v___y_1882_ = v___x_1892_;
goto v___jp_1881_;
}
v___jp_1881_:
{
if (v___y_1882_ == 0)
{
uint32_t v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = 39;
v___x_1884_ = lean_uint32_dec_eq(v_c_1880_, v___x_1883_);
if (v___x_1884_ == 0)
{
uint32_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = 114;
v___x_1886_ = lean_uint32_dec_eq(v_c_1880_, v___x_1885_);
if (v___x_1886_ == 0)
{
uint32_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = 110;
v___x_1888_ = lean_uint32_dec_eq(v_c_1880_, v___x_1887_);
if (v___x_1888_ == 0)
{
uint32_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = 116;
v___x_1890_ = lean_uint32_dec_eq(v_c_1880_, v___x_1889_);
return v___x_1890_;
}
else
{
return v___x_1888_;
}
}
else
{
return v___x_1886_;
}
}
else
{
return v___x_1884_;
}
}
else
{
return v___y_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1895_){
_start:
{
uint32_t v_c_boxed_1896_; uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_c_boxed_1896_ = lean_unbox_uint32(v_c_1895_);
lean_dec(v_c_1895_);
v_res_1897_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1896_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1903_ = 0;
v___x_1904_ = l_Lean_Parser_quotedCharCoreFn(v___x_1902_, v___x_1903_, v_a_1900_, v_a_1901_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1908_ = 1;
v___x_1909_ = l_Lean_Parser_quotedCharCoreFn(v___x_1907_, v___x_1908_, v_a_1905_, v_a_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1910_, lean_object* v_startPos_1911_, uint8_t v_includeWhitespace_1912_, lean_object* v_c_1913_, lean_object* v_s_1914_){
_start:
{
lean_object* v_pos_1915_; lean_object* v_errorMsg_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_pos_1915_ = lean_ctor_get(v_s_1914_, 2);
v_errorMsg_1916_ = lean_ctor_get(v_s_1914_, 4);
v___x_1917_ = lean_box(0);
v___x_1918_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1916_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_dec_ref(v_c_1913_);
lean_dec(v_startPos_1911_);
lean_dec(v_n_1910_);
return v_s_1914_;
}
else
{
lean_object* v_toInputContext_1919_; lean_object* v_inputString_1920_; lean_object* v_endPos_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1943_; 
lean_inc(v_pos_1915_);
v_toInputContext_1919_ = lean_ctor_get(v_c_1913_, 0);
lean_inc_ref(v_toInputContext_1919_);
v_inputString_1920_ = lean_ctor_get(v_toInputContext_1919_, 0);
v_endPos_1921_ = lean_ctor_get(v_toInputContext_1919_, 3);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_toInputContext_1919_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; lean_object* v_unused_1945_; 
v_unused_1944_ = lean_ctor_get(v_toInputContext_1919_, 2);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_toInputContext_1919_, 1);
lean_dec(v_unused_1945_);
v___x_1923_ = v_toInputContext_1919_;
v_isShared_1924_ = v_isSharedCheck_1943_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_endPos_1921_);
lean_inc(v_inputString_1920_);
lean_dec(v_toInputContext_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1943_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v_leading_1925_; lean_object* v_val_1926_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1936_; lean_object* v_pos_1937_; 
lean_inc(v_startPos_1911_);
v_leading_1925_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1913_, v_startPos_1911_);
v_val_1926_ = lean_string_utf8_extract(v_inputString_1920_, v_startPos_1911_, v_pos_1915_);
if (v_includeWhitespace_1912_ == 0)
{
lean_dec_ref(v_c_1913_);
lean_inc(v_pos_1915_);
v___y_1936_ = v_s_1914_;
v_pos_1937_ = v_pos_1915_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1941_; lean_object* v_pos_1942_; 
v___x_1941_ = l_Lean_Parser_whitespace(v_c_1913_, v_s_1914_);
v_pos_1942_ = lean_ctor_get(v___x_1941_, 2);
lean_inc(v_pos_1942_);
v___y_1936_ = v___x_1941_;
v_pos_1937_ = v_pos_1942_;
goto v___jp_1935_;
}
v___jp_1927_:
{
lean_object* v_info_1931_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 3, v_pos_1915_);
lean_ctor_set(v___x_1923_, 2, v___y_1929_);
lean_ctor_set(v___x_1923_, 1, v_startPos_1911_);
lean_ctor_set(v___x_1923_, 0, v_leading_1925_);
v_info_1931_ = v___x_1923_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_leading_1925_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_startPos_1911_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v___y_1929_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v_pos_1915_);
v_info_1931_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = l_Lean_Syntax_mkLit(v_n_1910_, v_val_1926_, v_info_1931_);
v___x_1933_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1928_, v___x_1932_);
return v___x_1933_;
}
}
v___jp_1935_:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_nat_dec_le(v_pos_1937_, v_endPos_1921_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec(v_pos_1937_);
lean_inc(v_pos_1915_);
v___x_1939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1939_, 0, v_inputString_1920_);
lean_ctor_set(v___x_1939_, 1, v_pos_1915_);
lean_ctor_set(v___x_1939_, 2, v_endPos_1921_);
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___x_1939_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1940_; 
lean_dec(v_endPos_1921_);
lean_inc(v_pos_1915_);
v___x_1940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1940_, 0, v_inputString_1920_);
lean_ctor_set(v___x_1940_, 1, v_pos_1915_);
lean_ctor_set(v___x_1940_, 2, v_pos_1937_);
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___x_1940_;
goto v___jp_1927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1946_, lean_object* v_startPos_1947_, lean_object* v_includeWhitespace_1948_, lean_object* v_c_1949_, lean_object* v_s_1950_){
_start:
{
uint8_t v_includeWhitespace_boxed_1951_; lean_object* v_res_1952_; 
v_includeWhitespace_boxed_1951_ = lean_unbox(v_includeWhitespace_1948_);
v_res_1952_ = l_Lean_Parser_mkNodeToken(v_n_1946_, v_startPos_1947_, v_includeWhitespace_boxed_1951_, v_c_1949_, v_s_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1957_, lean_object* v_c_1958_, lean_object* v_s_1959_){
_start:
{
lean_object* v_pos_1960_; lean_object* v_toInputContext_1961_; uint8_t v___x_1962_; 
v_pos_1960_ = lean_ctor_get(v_s_1959_, 2);
v_toInputContext_1961_ = lean_ctor_get(v_c_1958_, 0);
v___x_1962_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1961_, v_pos_1960_);
if (v___x_1962_ == 0)
{
lean_object* v_inputString_1963_; uint8_t v___x_1964_; lean_object* v___y_1966_; uint32_t v_curr_1981_; lean_object* v___x_1982_; lean_object* v_s_1983_; uint32_t v___x_1984_; uint8_t v___x_1985_; 
v_inputString_1963_ = lean_ctor_get(v_toInputContext_1961_, 0);
v___x_1964_ = 1;
v_curr_1981_ = lean_string_utf8_get_fast(v_inputString_1963_, v_pos_1960_);
v___x_1982_ = lean_string_utf8_next_fast(v_inputString_1963_, v_pos_1960_);
v_s_1983_ = l_Lean_Parser_ParserState_setPos(v_s_1959_, v___x_1982_);
v___x_1984_ = 92;
v___x_1985_ = lean_uint32_dec_eq(v_curr_1981_, v___x_1984_);
if (v___x_1985_ == 0)
{
v___y_1966_ = v_s_1983_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_1986_; 
lean_inc_ref(v_c_1958_);
v___x_1986_ = l_Lean_Parser_quotedCharFn(v_c_1958_, v_s_1983_);
v___y_1966_ = v___x_1986_;
goto v___jp_1965_;
}
v___jp_1965_:
{
lean_object* v_pos_1967_; lean_object* v_errorMsg_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_pos_1967_ = lean_ctor_get(v___y_1966_, 2);
v_errorMsg_1968_ = lean_ctor_get(v___y_1966_, 4);
v___x_1969_ = lean_box(0);
v___x_1970_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_dec_ref(v_c_1958_);
lean_dec(v_startPos_1957_);
return v___y_1966_;
}
else
{
if (v___x_1962_ == 0)
{
uint32_t v_curr_1971_; lean_object* v___x_1972_; lean_object* v_s_1973_; uint32_t v___x_1974_; uint8_t v___x_1975_; 
v_curr_1971_ = lean_string_utf8_get(v_inputString_1963_, v_pos_1967_);
v___x_1972_ = lean_string_utf8_next(v_inputString_1963_, v_pos_1967_);
v_s_1973_ = l_Lean_Parser_ParserState_setPos(v___y_1966_, v___x_1972_);
v___x_1974_ = 39;
v___x_1975_ = lean_uint32_dec_eq(v_curr_1971_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref(v_c_1958_);
lean_dec(v_startPos_1957_);
v___x_1976_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1977_ = lean_box(0);
v___x_1978_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1973_, v___x_1976_, v___x_1977_, v___x_1964_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1980_ = l_Lean_Parser_mkNodeToken(v___x_1979_, v_startPos_1957_, v___x_1964_, v_c_1958_, v_s_1973_);
return v___x_1980_;
}
}
else
{
lean_dec_ref(v_c_1958_);
lean_dec(v_startPos_1957_);
return v___y_1966_;
}
}
}
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec_ref(v_c_1958_);
lean_dec(v_startPos_1957_);
v___x_1987_ = lean_box(0);
v___x_1988_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1959_, v___x_1987_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_1993_, lean_object* v_includeWhitespace_1994_, lean_object* v_c_1995_, lean_object* v_s_1996_){
_start:
{
uint8_t v_includeWhitespace_boxed_1997_; lean_object* v_res_1998_; 
v_includeWhitespace_boxed_1997_ = lean_unbox(v_includeWhitespace_1994_);
v_res_1998_ = l_Lean_Parser_strLitFnAux(v_startPos_1993_, v_includeWhitespace_boxed_1997_, v_c_1995_, v_s_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_1999_, uint8_t v_includeWhitespace_2000_, lean_object* v_c_2001_, lean_object* v_s_2002_){
_start:
{
lean_object* v_pos_2003_; lean_object* v_toInputContext_2004_; uint8_t v___x_2005_; 
v_pos_2003_ = lean_ctor_get(v_s_2002_, 2);
v_toInputContext_2004_ = lean_ctor_get(v_c_2001_, 0);
v___x_2005_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2004_, v_pos_2003_);
if (v___x_2005_ == 0)
{
lean_object* v_inputString_2006_; uint32_t v_curr_2007_; lean_object* v___x_2008_; lean_object* v_s_2009_; uint32_t v___x_2010_; uint8_t v___x_2011_; 
v_inputString_2006_ = lean_ctor_get(v_toInputContext_2004_, 0);
v_curr_2007_ = lean_string_utf8_get_fast(v_inputString_2006_, v_pos_2003_);
v___x_2008_ = lean_string_utf8_next_fast(v_inputString_2006_, v_pos_2003_);
v_s_2009_ = l_Lean_Parser_ParserState_setPos(v_s_2002_, v___x_2008_);
v___x_2010_ = 34;
v___x_2011_ = lean_uint32_dec_eq(v_curr_2007_, v___x_2010_);
if (v___x_2011_ == 0)
{
uint32_t v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = 92;
v___x_2013_ = lean_uint32_dec_eq(v_curr_2007_, v___x_2012_);
if (v___x_2013_ == 0)
{
v_s_2002_ = v_s_2009_;
goto _start;
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2016_ = lean_box(v___x_2013_);
v___x_2017_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2017_, 0, v_startPos_1999_);
lean_closure_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = l_Lean_Parser_andthenFn(v___x_2015_, v___x_2017_, v_c_2001_, v_s_2009_);
return v___x_2018_;
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2020_ = l_Lean_Parser_mkNodeToken(v___x_2019_, v_startPos_1999_, v_includeWhitespace_2000_, v_c_2001_, v_s_2009_);
return v___x_2020_;
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v_c_2001_);
v___x_2021_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2022_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2002_, v___x_2021_, v_startPos_1999_);
return v___x_2022_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2023_, lean_object* v_i_2024_){
_start:
{
lean_object* v_toInputContext_2025_; uint8_t v___x_2026_; 
v_toInputContext_2025_ = lean_ctor_get(v_c_2023_, 0);
v___x_2026_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2025_, v_i_2024_);
if (v___x_2026_ == 0)
{
lean_object* v_inputString_2027_; uint32_t v_curr_2028_; uint32_t v___x_2029_; uint8_t v___x_2030_; 
v_inputString_2027_ = lean_ctor_get(v_toInputContext_2025_, 0);
v_curr_2028_ = lean_string_utf8_get_fast(v_inputString_2027_, v_i_2024_);
v___x_2029_ = 35;
v___x_2030_ = lean_uint32_dec_eq(v_curr_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
uint32_t v___x_2031_; uint8_t v___x_2032_; 
lean_dec(v_i_2024_);
v___x_2031_ = 34;
v___x_2032_ = lean_uint32_dec_eq(v_curr_2028_, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_string_utf8_next_fast(v_inputString_2027_, v_i_2024_);
lean_dec(v_i_2024_);
v_i_2024_ = v___x_2033_;
goto _start;
}
}
else
{
uint8_t v___x_2035_; 
lean_dec(v_i_2024_);
v___x_2035_ = 0;
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2036_, lean_object* v_i_2037_){
_start:
{
uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_res_2038_ = l_Lean_Parser_isRawStrLitStart(v_c_2036_, v_i_2037_);
lean_dec_ref(v_c_2036_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2041_, lean_object* v_s_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2044_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2042_, v___x_2043_, v_startPos_2041_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2045_, lean_object* v_num_2046_, lean_object* v_closingNum_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_pos_2050_; lean_object* v_toInputContext_2051_; uint8_t v___x_2052_; 
v_pos_2050_ = lean_ctor_get(v_a_2049_, 2);
v_toInputContext_2051_ = lean_ctor_get(v_a_2048_, 0);
v___x_2052_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2051_, v_pos_2050_);
if (v___x_2052_ == 0)
{
lean_object* v_inputString_2053_; uint32_t v_curr_2054_; lean_object* v___x_2055_; lean_object* v_s_2056_; uint32_t v___x_2057_; uint8_t v___x_2058_; 
v_inputString_2053_ = lean_ctor_get(v_toInputContext_2051_, 0);
v_curr_2054_ = lean_string_utf8_get_fast(v_inputString_2053_, v_pos_2050_);
v___x_2055_ = lean_string_utf8_next_fast(v_inputString_2053_, v_pos_2050_);
v_s_2056_ = l_Lean_Parser_ParserState_setPos(v_a_2049_, v___x_2055_);
v___x_2057_ = 35;
v___x_2058_ = lean_uint32_dec_eq(v_curr_2054_, v___x_2057_);
if (v___x_2058_ == 0)
{
uint32_t v___x_2059_; uint8_t v___x_2060_; 
lean_dec(v_closingNum_2047_);
v___x_2059_ = 34;
v___x_2060_ = lean_uint32_dec_eq(v_curr_2054_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2045_, v_num_2046_, v_a_2048_, v_s_2056_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_unsigned_to_nat(0u);
v_closingNum_2047_ = v___x_2062_;
v_a_2049_ = v_s_2056_;
goto _start;
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_nat_add(v_closingNum_2047_, v___x_2064_);
lean_dec(v_closingNum_2047_);
v___x_2066_ = lean_nat_dec_eq(v___x_2065_, v_num_2046_);
if (v___x_2066_ == 0)
{
v_closingNum_2047_ = v___x_2065_;
v_a_2049_ = v_s_2056_;
goto _start;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v___x_2065_);
v___x_2068_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2069_ = l_Lean_Parser_mkNodeToken(v___x_2068_, v_startPos_2045_, v___x_2066_, v_a_2048_, v_s_2056_);
return v___x_2069_;
}
}
}
else
{
lean_object* v___x_2070_; 
lean_dec_ref(v_a_2048_);
lean_dec(v_closingNum_2047_);
v___x_2070_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2045_, v_a_2049_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2071_, lean_object* v_num_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_pos_2075_; lean_object* v_toInputContext_2076_; uint8_t v___x_2077_; 
v_pos_2075_ = lean_ctor_get(v_a_2074_, 2);
v_toInputContext_2076_ = lean_ctor_get(v_a_2073_, 0);
v___x_2077_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2076_, v_pos_2075_);
if (v___x_2077_ == 0)
{
lean_object* v_inputString_2078_; uint32_t v_curr_2079_; lean_object* v___x_2080_; lean_object* v_s_2081_; uint32_t v___x_2082_; uint8_t v___x_2083_; 
v_inputString_2078_ = lean_ctor_get(v_toInputContext_2076_, 0);
v_curr_2079_ = lean_string_utf8_get_fast(v_inputString_2078_, v_pos_2075_);
v___x_2080_ = lean_string_utf8_next_fast(v_inputString_2078_, v_pos_2075_);
v_s_2081_ = l_Lean_Parser_ParserState_setPos(v_a_2074_, v___x_2080_);
v___x_2082_ = 34;
v___x_2083_ = lean_uint32_dec_eq(v_curr_2079_, v___x_2082_);
if (v___x_2083_ == 0)
{
v_a_2074_ = v_s_2081_;
goto _start;
}
else
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_nat_dec_eq(v_num_2072_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2071_, v_num_2072_, v___x_2085_, v_a_2073_, v_s_2081_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2089_ = l_Lean_Parser_mkNodeToken(v___x_2088_, v_startPos_2071_, v___x_2086_, v_a_2073_, v_s_2081_);
return v___x_2089_;
}
}
}
else
{
lean_object* v___x_2090_; 
lean_dec_ref(v_a_2073_);
v___x_2090_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2071_, v_a_2074_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2091_, lean_object* v_num_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2091_, v_num_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_num_2092_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2096_, lean_object* v_num_2097_, lean_object* v_closingNum_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2096_, v_num_2097_, v_closingNum_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_num_2097_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2102_, lean_object* v_num_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_pos_2106_; lean_object* v_toInputContext_2107_; uint8_t v___x_2108_; 
v_pos_2106_ = lean_ctor_get(v_a_2105_, 2);
v_toInputContext_2107_ = lean_ctor_get(v_a_2104_, 0);
v___x_2108_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2107_, v_pos_2106_);
if (v___x_2108_ == 0)
{
lean_object* v_inputString_2109_; uint32_t v_curr_2110_; lean_object* v___x_2111_; lean_object* v_s_2112_; uint32_t v___x_2113_; uint8_t v___x_2114_; 
v_inputString_2109_ = lean_ctor_get(v_toInputContext_2107_, 0);
v_curr_2110_ = lean_string_utf8_get_fast(v_inputString_2109_, v_pos_2106_);
v___x_2111_ = lean_string_utf8_next_fast(v_inputString_2109_, v_pos_2106_);
v_s_2112_ = l_Lean_Parser_ParserState_setPos(v_a_2105_, v___x_2111_);
v___x_2113_ = 35;
v___x_2114_ = lean_uint32_dec_eq(v_curr_2110_, v___x_2113_);
if (v___x_2114_ == 0)
{
uint32_t v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = 34;
v___x_2116_ = lean_uint32_dec_eq(v_curr_2110_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref(v_a_2104_);
lean_dec(v_num_2103_);
v___x_2117_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2102_, v_s_2112_);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; 
v___x_2118_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2102_, v_num_2103_, v_a_2104_, v_s_2112_);
lean_dec(v_num_2103_);
return v___x_2118_;
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_unsigned_to_nat(1u);
v___x_2120_ = lean_nat_add(v_num_2103_, v___x_2119_);
lean_dec(v_num_2103_);
v_num_2103_ = v___x_2120_;
v_a_2105_ = v_s_2112_;
goto _start;
}
}
else
{
lean_object* v___x_2122_; 
lean_dec_ref(v_a_2104_);
lean_dec(v_num_2103_);
v___x_2122_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2102_, v_a_2105_);
return v___x_2122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2123_, v___x_2126_, v_a_2124_, v_a_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2129_, lean_object* v_expecting_2130_, uint8_t v_needDigit_2131_, lean_object* v_c_2132_, lean_object* v_s_2133_){
_start:
{
lean_object* v_pos_2134_; lean_object* v_toInputContext_2135_; uint8_t v___x_2136_; 
v_pos_2134_ = lean_ctor_get(v_s_2133_, 2);
v_toInputContext_2135_ = lean_ctor_get(v_c_2132_, 0);
v___x_2136_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2135_, v_pos_2134_);
if (v___x_2136_ == 0)
{
lean_object* v_inputString_2137_; uint8_t v___x_2138_; uint32_t v_curr_2139_; uint32_t v___x_2140_; uint8_t v___x_2141_; 
v_inputString_2137_ = lean_ctor_get(v_toInputContext_2135_, 0);
v___x_2138_ = 1;
v_curr_2139_ = lean_string_utf8_get_fast(v_inputString_2137_, v_pos_2134_);
v___x_2140_ = 95;
v___x_2141_ = lean_uint32_dec_eq(v_curr_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = lean_box_uint32(v_curr_2139_);
lean_inc_ref(v_isDigit_2129_);
v___x_2143_ = lean_apply_1(v_isDigit_2129_, v___x_2142_);
v___x_2144_ = lean_unbox(v___x_2143_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_isDigit_2129_);
if (v_needDigit_2131_ == 0)
{
lean_dec_ref(v_expecting_2130_);
return v_s_2133_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2145_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_expecting_2130_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2133_, v___x_2145_, v___x_2147_, v___x_2138_);
return v___x_2148_;
}
}
else
{
lean_object* v___x_2149_; 
lean_inc(v_pos_2134_);
v___x_2149_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2133_, v_c_2132_, v_pos_2134_);
lean_dec(v_pos_2134_);
v_needDigit_2131_ = v___x_2141_;
v_s_2133_ = v___x_2149_;
goto _start;
}
}
else
{
lean_object* v___x_2151_; 
lean_inc(v_pos_2134_);
v___x_2151_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2133_, v_c_2132_, v_pos_2134_);
lean_dec(v_pos_2134_);
v_needDigit_2131_ = v___x_2138_;
v_s_2133_ = v___x_2151_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2129_);
if (v_needDigit_2131_ == 0)
{
lean_dec_ref(v_expecting_2130_);
return v_s_2133_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_expecting_2130_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2133_, v___x_2154_);
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2156_, lean_object* v_expecting_2157_, lean_object* v_needDigit_2158_, lean_object* v_c_2159_, lean_object* v_s_2160_){
_start:
{
uint8_t v_needDigit_boxed_2161_; lean_object* v_res_2162_; 
v_needDigit_boxed_2161_ = lean_unbox(v_needDigit_2158_);
v_res_2162_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2156_, v_expecting_2157_, v_needDigit_boxed_2161_, v_c_2159_, v_s_2160_);
lean_dec_ref(v_c_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2163_){
_start:
{
uint32_t v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = 48;
v___x_2165_ = lean_uint32_dec_le(v___x_2164_, v_c_2163_);
if (v___x_2165_ == 0)
{
return v___x_2165_;
}
else
{
uint32_t v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = 57;
v___x_2167_ = lean_uint32_dec_le(v_c_2163_, v___x_2166_);
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2168_){
_start:
{
uint32_t v_c_boxed_2169_; uint8_t v_res_2170_; lean_object* v_r_2171_; 
v_c_boxed_2169_ = lean_unbox_uint32(v_c_2168_);
lean_dec(v_c_2168_);
v_res_2170_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2169_);
v_r_2171_ = lean_box(v_res_2170_);
return v_r_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2176_, lean_object* v_c_2177_, lean_object* v_s_2178_, uint8_t v_hasBareDot_2179_){
_start:
{
lean_object* v_toInputContext_2180_; lean_object* v_pos_2181_; uint8_t v___x_2182_; 
v_toInputContext_2180_ = lean_ctor_get(v_c_2177_, 0);
v_pos_2181_ = lean_ctor_get(v_s_2178_, 2);
v___x_2182_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2180_, v_pos_2181_);
if (v___x_2182_ == 0)
{
lean_object* v_inputString_2183_; lean_object* v___f_2184_; uint8_t v___x_2185_; lean_object* v___y_2187_; uint8_t v___y_2188_; lean_object* v___y_2196_; lean_object* v___y_2203_; lean_object* v___y_2204_; uint32_t v_curr_2218_; uint8_t v___y_2220_; uint8_t v___y_2224_; uint32_t v___x_2233_; uint8_t v___x_2234_; 
v_inputString_2183_ = lean_ctor_get(v_toInputContext_2180_, 0);
v___f_2184_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2185_ = 1;
v_curr_2218_ = lean_string_utf8_get_fast(v_inputString_2183_, v_pos_2181_);
v___x_2233_ = 101;
v___x_2234_ = lean_uint32_dec_eq(v_curr_2218_, v___x_2233_);
if (v___x_2234_ == 0)
{
uint32_t v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = 69;
v___x_2236_ = lean_uint32_dec_eq(v_curr_2218_, v___x_2235_);
if (v___x_2236_ == 0)
{
if (v_hasBareDot_2179_ == 0)
{
lean_dec(v_startPos_2176_);
return v_s_2178_;
}
else
{
uint32_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = 65;
v___x_2238_ = lean_uint32_dec_le(v___x_2237_, v_curr_2218_);
if (v___x_2238_ == 0)
{
goto v___jp_2228_;
}
else
{
uint32_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = 90;
v___x_2240_ = lean_uint32_dec_le(v_curr_2218_, v___x_2239_);
if (v___x_2240_ == 0)
{
goto v___jp_2228_;
}
else
{
goto v___jp_2213_;
}
}
}
}
else
{
lean_dec(v_startPos_2176_);
goto v___jp_2206_;
}
}
else
{
lean_dec(v_startPos_2176_);
goto v___jp_2206_;
}
v___jp_2186_:
{
if (v___y_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v___y_2187_);
v___x_2189_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2190_ = lean_box(0);
v___x_2191_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2178_, v___x_2189_, v___x_2190_, v___x_2185_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2193_ = l_Lean_Parser_ParserState_setPos(v_s_2178_, v___y_2187_);
v___x_2194_ = l_Lean_Parser_takeDigitsFn(v___f_2184_, v___x_2192_, v___x_2182_, v_c_2177_, v___x_2193_);
return v___x_2194_;
}
}
v___jp_2195_:
{
uint32_t v_curr_2197_; uint32_t v___x_2198_; uint8_t v___x_2199_; 
v_curr_2197_ = lean_string_utf8_get(v_inputString_2183_, v___y_2196_);
v___x_2198_ = 48;
v___x_2199_ = lean_uint32_dec_le(v___x_2198_, v_curr_2197_);
if (v___x_2199_ == 0)
{
v___y_2187_ = v___y_2196_;
v___y_2188_ = v___x_2199_;
goto v___jp_2186_;
}
else
{
uint32_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = 57;
v___x_2201_ = lean_uint32_dec_le(v_curr_2197_, v___x_2200_);
v___y_2187_ = v___y_2196_;
v___y_2188_ = v___x_2201_;
goto v___jp_2186_;
}
}
v___jp_2202_:
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_string_utf8_next(v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
v___y_2196_ = v___x_2205_;
goto v___jp_2195_;
}
v___jp_2206_:
{
lean_object* v_i_2207_; uint32_t v___x_2208_; uint32_t v___x_2209_; uint8_t v___x_2210_; 
v_i_2207_ = lean_string_utf8_next(v_inputString_2183_, v_pos_2181_);
v___x_2208_ = lean_string_utf8_get(v_inputString_2183_, v_i_2207_);
v___x_2209_ = 45;
v___x_2210_ = lean_uint32_dec_eq(v___x_2208_, v___x_2209_);
if (v___x_2210_ == 0)
{
uint32_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = 43;
v___x_2212_ = lean_uint32_dec_eq(v___x_2208_, v___x_2211_);
if (v___x_2212_ == 0)
{
v___y_2196_ = v_i_2207_;
goto v___jp_2195_;
}
else
{
v___y_2203_ = v_inputString_2183_;
v___y_2204_ = v_i_2207_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v_inputString_2183_;
v___y_2204_ = v_i_2207_;
goto v___jp_2202_;
}
}
v___jp_2213_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = l_Lean_Parser_ParserState_setPos(v_s_2178_, v_startPos_2176_);
v___x_2215_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2216_ = lean_box(0);
v___x_2217_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2214_, v___x_2215_, v___x_2216_, v___x_2185_);
return v___x_2217_;
}
v___jp_2219_:
{
if (v___y_2220_ == 0)
{
uint32_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = 171;
v___x_2222_ = lean_uint32_dec_eq(v_curr_2218_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_dec(v_startPos_2176_);
return v_s_2178_;
}
else
{
goto v___jp_2213_;
}
}
else
{
goto v___jp_2213_;
}
}
v___jp_2223_:
{
if (v___y_2224_ == 0)
{
uint32_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = 95;
v___x_2226_ = lean_uint32_dec_eq(v_curr_2218_, v___x_2225_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_isLetterLike(v_curr_2218_);
v___y_2220_ = v___x_2227_;
goto v___jp_2219_;
}
else
{
v___y_2220_ = v___x_2226_;
goto v___jp_2219_;
}
}
else
{
goto v___jp_2213_;
}
}
v___jp_2228_:
{
uint32_t v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = 97;
v___x_2230_ = lean_uint32_dec_le(v___x_2229_, v_curr_2218_);
if (v___x_2230_ == 0)
{
v___y_2224_ = v___x_2230_;
goto v___jp_2223_;
}
else
{
uint32_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = 122;
v___x_2232_ = lean_uint32_dec_le(v_curr_2218_, v___x_2231_);
v___y_2224_ = v___x_2232_;
goto v___jp_2223_;
}
}
}
else
{
lean_dec(v_startPos_2176_);
return v_s_2178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2241_, lean_object* v_c_2242_, lean_object* v_s_2243_, lean_object* v_hasBareDot_2244_){
_start:
{
uint8_t v_hasBareDot_boxed_2245_; lean_object* v_res_2246_; 
v_hasBareDot_boxed_2245_ = lean_unbox(v_hasBareDot_2244_);
v_res_2246_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2241_, v_c_2242_, v_s_2243_, v_hasBareDot_boxed_2245_);
lean_dec_ref(v_c_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2247_, lean_object* v_s_2248_){
_start:
{
lean_object* v_toInputContext_2249_; lean_object* v_pos_2250_; lean_object* v_inputString_2251_; uint32_t v_curr_2252_; uint32_t v___x_2253_; uint8_t v___x_2254_; 
v_toInputContext_2249_ = lean_ctor_get(v_c_2247_, 0);
v_pos_2250_ = lean_ctor_get(v_s_2248_, 2);
v_inputString_2251_ = lean_ctor_get(v_toInputContext_2249_, 0);
v_curr_2252_ = lean_string_utf8_get(v_inputString_2251_, v_pos_2250_);
v___x_2253_ = 46;
v___x_2254_ = lean_uint32_dec_eq(v_curr_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2256_, 0, v_s_2248_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v___f_2257_; lean_object* v_i_2258_; uint8_t v___y_2260_; uint32_t v_curr_2270_; uint32_t v___x_2271_; uint8_t v___x_2272_; 
v___f_2257_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_i_2258_ = lean_string_utf8_next(v_inputString_2251_, v_pos_2250_);
v_curr_2270_ = lean_string_utf8_get(v_inputString_2251_, v_i_2258_);
v___x_2271_ = 48;
v___x_2272_ = lean_uint32_dec_le(v___x_2271_, v_curr_2270_);
if (v___x_2272_ == 0)
{
v___y_2260_ = v___x_2272_;
goto v___jp_2259_;
}
else
{
uint32_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = 57;
v___x_2274_ = lean_uint32_dec_le(v_curr_2270_, v___x_2273_);
v___y_2260_ = v___x_2274_;
goto v___jp_2259_;
}
v___jp_2259_:
{
if (v___y_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = l_Lean_Parser_ParserState_setPos(v_s_2248_, v_i_2258_);
v___x_2262_ = lean_box(v___x_2254_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
return v___x_2263_;
}
else
{
lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2265_ = 0;
v___x_2266_ = l_Lean_Parser_ParserState_setPos(v_s_2248_, v_i_2258_);
v___x_2267_ = l_Lean_Parser_takeDigitsFn(v___f_2257_, v___x_2264_, v___x_2265_, v_c_2247_, v___x_2266_);
v___x_2268_ = lean_box(v___x_2265_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2275_, lean_object* v_s_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2275_, v_s_2276_);
lean_dec_ref(v_c_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2281_, uint8_t v_includeWhitespace_2282_, lean_object* v_c_2283_, lean_object* v_s_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v_fst_2286_; lean_object* v_snd_2287_; uint8_t v___x_2288_; lean_object* v_s_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2285_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2283_, v_s_2284_);
v_fst_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_fst_2286_);
v_snd_2287_ = lean_ctor_get(v___x_2285_, 1);
lean_inc(v_snd_2287_);
lean_dec_ref(v___x_2285_);
v___x_2288_ = lean_unbox(v_snd_2287_);
lean_dec(v_snd_2287_);
lean_inc(v_startPos_2281_);
v_s_2289_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2281_, v_c_2283_, v_fst_2286_, v___x_2288_);
v___x_2290_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2291_ = l_Lean_Parser_mkNodeToken(v___x_2290_, v_startPos_2281_, v_includeWhitespace_2282_, v_c_2283_, v_s_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2292_, lean_object* v_includeWhitespace_2293_, lean_object* v_c_2294_, lean_object* v_s_2295_){
_start:
{
uint8_t v_includeWhitespace_boxed_2296_; lean_object* v_res_2297_; 
v_includeWhitespace_boxed_2296_ = lean_unbox(v_includeWhitespace_2293_);
v_res_2297_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2292_, v_includeWhitespace_boxed_2296_, v_c_2294_, v_s_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2301_, uint8_t v_includeWhitespace_2302_, lean_object* v_c_2303_, lean_object* v_s_2304_){
_start:
{
lean_object* v___f_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; lean_object* v_s_2308_; lean_object* v_pos_2309_; lean_object* v_toInputContext_2310_; uint8_t v___x_2311_; 
v___f_2305_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2306_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2307_ = 0;
v_s_2308_ = l_Lean_Parser_takeDigitsFn(v___f_2305_, v___x_2306_, v___x_2307_, v_c_2303_, v_s_2304_);
v_pos_2309_ = lean_ctor_get(v_s_2308_, 2);
lean_inc(v_pos_2309_);
v_toInputContext_2310_ = lean_ctor_get(v_c_2303_, 0);
v___x_2311_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2310_, v_pos_2309_);
if (v___x_2311_ == 0)
{
lean_object* v_inputString_2312_; uint32_t v_curr_2313_; uint8_t v___y_2327_; lean_object* v_j_2330_; uint8_t v___x_2336_; 
v_inputString_2312_ = lean_ctor_get(v_toInputContext_2310_, 0);
v_curr_2313_ = lean_string_utf8_get_fast(v_inputString_2312_, v_pos_2309_);
v_j_2330_ = lean_string_utf8_next(v_inputString_2312_, v_pos_2309_);
lean_dec(v_pos_2309_);
v___x_2336_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2310_, v_j_2330_);
if (v___x_2336_ == 0)
{
goto v___jp_2331_;
}
else
{
if (v___x_2311_ == 0)
{
lean_dec(v_j_2330_);
goto v___jp_2314_;
}
else
{
goto v___jp_2331_;
}
}
v___jp_2314_:
{
uint32_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = 46;
v___x_2316_ = lean_uint32_dec_eq(v_curr_2313_, v___x_2315_);
if (v___x_2316_ == 0)
{
uint32_t v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = 101;
v___x_2318_ = lean_uint32_dec_eq(v_curr_2313_, v___x_2317_);
if (v___x_2318_ == 0)
{
uint32_t v___x_2319_; uint8_t v___x_2320_; 
v___x_2319_ = 69;
v___x_2320_ = lean_uint32_dec_eq(v_curr_2313_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2322_ = l_Lean_Parser_mkNodeToken(v___x_2321_, v_startPos_2301_, v_includeWhitespace_2302_, v_c_2303_, v_s_2308_);
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; 
v___x_2323_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2301_, v_includeWhitespace_2302_, v_c_2303_, v_s_2308_);
return v___x_2323_;
}
}
else
{
lean_object* v___x_2324_; 
v___x_2324_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2301_, v_includeWhitespace_2302_, v_c_2303_, v_s_2308_);
return v___x_2324_;
}
}
else
{
lean_object* v___x_2325_; 
v___x_2325_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2301_, v_includeWhitespace_2302_, v_c_2303_, v_s_2308_);
return v___x_2325_;
}
}
v___jp_2326_:
{
if (v___y_2327_ == 0)
{
goto v___jp_2314_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2329_ = l_Lean_Parser_mkNodeToken(v___x_2328_, v_startPos_2301_, v_includeWhitespace_2302_, v_c_2303_, v_s_2308_);
return v___x_2329_;
}
}
v___jp_2331_:
{
uint32_t v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = 46;
v___x_2333_ = lean_uint32_dec_eq(v_curr_2313_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec(v_j_2330_);
v___y_2327_ = v___x_2333_;
goto v___jp_2326_;
}
else
{
uint32_t v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_string_utf8_get_fast(v_inputString_2312_, v_j_2330_);
lean_dec(v_j_2330_);
v___x_2335_ = lean_uint32_dec_eq(v___x_2334_, v___x_2332_);
v___y_2327_ = v___x_2335_;
goto v___jp_2326_;
}
}
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_pos_2309_);
v___x_2337_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2338_ = l_Lean_Parser_mkNodeToken(v___x_2337_, v_startPos_2301_, v___x_2311_, v_c_2303_, v_s_2308_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2339_, lean_object* v_includeWhitespace_2340_, lean_object* v_c_2341_, lean_object* v_s_2342_){
_start:
{
uint8_t v_includeWhitespace_boxed_2343_; lean_object* v_res_2344_; 
v_includeWhitespace_boxed_2343_ = lean_unbox(v_includeWhitespace_2340_);
v_res_2344_ = l_Lean_Parser_decimalNumberFn(v_startPos_2339_, v_includeWhitespace_boxed_2343_, v_c_2341_, v_s_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2345_){
_start:
{
uint32_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = 48;
v___x_2347_ = lean_uint32_dec_eq(v_c_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
uint32_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = 49;
v___x_2349_ = lean_uint32_dec_eq(v_c_2345_, v___x_2348_);
return v___x_2349_;
}
else
{
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2350_){
_start:
{
uint32_t v_c_boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_c_boxed_2351_ = lean_unbox_uint32(v_c_2350_);
lean_dec(v_c_2350_);
v_res_2352_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2351_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2356_, uint8_t v_includeWhitespace_2357_, lean_object* v_c_2358_, lean_object* v_s_2359_){
_start:
{
lean_object* v___f_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v_s_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___f_2360_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2361_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2362_ = 1;
v_s_2363_ = l_Lean_Parser_takeDigitsFn(v___f_2360_, v___x_2361_, v___x_2362_, v_c_2358_, v_s_2359_);
v___x_2364_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2365_ = l_Lean_Parser_mkNodeToken(v___x_2364_, v_startPos_2356_, v_includeWhitespace_2357_, v_c_2358_, v_s_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2366_, lean_object* v_includeWhitespace_2367_, lean_object* v_c_2368_, lean_object* v_s_2369_){
_start:
{
uint8_t v_includeWhitespace_boxed_2370_; lean_object* v_res_2371_; 
v_includeWhitespace_boxed_2370_ = lean_unbox(v_includeWhitespace_2367_);
v_res_2371_ = l_Lean_Parser_binNumberFn(v_startPos_2366_, v_includeWhitespace_boxed_2370_, v_c_2368_, v_s_2369_);
return v_res_2371_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2372_){
_start:
{
uint32_t v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = 48;
v___x_2374_ = lean_uint32_dec_le(v___x_2373_, v_c_2372_);
if (v___x_2374_ == 0)
{
return v___x_2374_;
}
else
{
uint32_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = 55;
v___x_2376_ = lean_uint32_dec_le(v_c_2372_, v___x_2375_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2377_){
_start:
{
uint32_t v_c_boxed_2378_; uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_c_boxed_2378_ = lean_unbox_uint32(v_c_2377_);
lean_dec(v_c_2377_);
v_res_2379_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2378_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2383_, uint8_t v_includeWhitespace_2384_, lean_object* v_c_2385_, lean_object* v_s_2386_){
_start:
{
lean_object* v___f_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; lean_object* v_s_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___f_2387_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2388_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2389_ = 1;
v_s_2390_ = l_Lean_Parser_takeDigitsFn(v___f_2387_, v___x_2388_, v___x_2389_, v_c_2385_, v_s_2386_);
v___x_2391_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2392_ = l_Lean_Parser_mkNodeToken(v___x_2391_, v_startPos_2383_, v_includeWhitespace_2384_, v_c_2385_, v_s_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2393_, lean_object* v_includeWhitespace_2394_, lean_object* v_c_2395_, lean_object* v_s_2396_){
_start:
{
uint8_t v_includeWhitespace_boxed_2397_; lean_object* v_res_2398_; 
v_includeWhitespace_boxed_2397_ = lean_unbox(v_includeWhitespace_2394_);
v_res_2398_ = l_Lean_Parser_octalNumberFn(v_startPos_2393_, v_includeWhitespace_boxed_2397_, v_c_2395_, v_s_2396_);
return v_res_2398_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2399_){
_start:
{
uint8_t v___y_2401_; uint8_t v___y_2407_; uint32_t v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = 48;
v___x_2413_ = lean_uint32_dec_le(v___x_2412_, v_c_2399_);
if (v___x_2413_ == 0)
{
v___y_2407_ = v___x_2413_;
goto v___jp_2406_;
}
else
{
uint32_t v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = 57;
v___x_2415_ = lean_uint32_dec_le(v_c_2399_, v___x_2414_);
v___y_2407_ = v___x_2415_;
goto v___jp_2406_;
}
v___jp_2400_:
{
if (v___y_2401_ == 0)
{
uint32_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = 65;
v___x_2403_ = lean_uint32_dec_le(v___x_2402_, v_c_2399_);
if (v___x_2403_ == 0)
{
return v___x_2403_;
}
else
{
uint32_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = 70;
v___x_2405_ = lean_uint32_dec_le(v_c_2399_, v___x_2404_);
return v___x_2405_;
}
}
else
{
return v___y_2401_;
}
}
v___jp_2406_:
{
if (v___y_2407_ == 0)
{
uint32_t v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = 97;
v___x_2409_ = lean_uint32_dec_le(v___x_2408_, v_c_2399_);
if (v___x_2409_ == 0)
{
v___y_2401_ = v___x_2409_;
goto v___jp_2400_;
}
else
{
uint32_t v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = 102;
v___x_2411_ = lean_uint32_dec_le(v_c_2399_, v___x_2410_);
v___y_2401_ = v___x_2411_;
goto v___jp_2400_;
}
}
else
{
return v___y_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2416_){
_start:
{
uint32_t v_c_boxed_2417_; uint8_t v_res_2418_; lean_object* v_r_2419_; 
v_c_boxed_2417_ = lean_unbox_uint32(v_c_2416_);
lean_dec(v_c_2416_);
v_res_2418_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2417_);
v_r_2419_ = lean_box(v_res_2418_);
return v_r_2419_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2420_){
_start:
{
uint8_t v___y_2422_; uint8_t v___y_2428_; uint32_t v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = 48;
v___x_2434_ = lean_uint32_dec_le(v___x_2433_, v___y_2420_);
if (v___x_2434_ == 0)
{
v___y_2428_ = v___x_2434_;
goto v___jp_2427_;
}
else
{
uint32_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = 57;
v___x_2436_ = lean_uint32_dec_le(v___y_2420_, v___x_2435_);
v___y_2428_ = v___x_2436_;
goto v___jp_2427_;
}
v___jp_2421_:
{
if (v___y_2422_ == 0)
{
uint32_t v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = 65;
v___x_2424_ = lean_uint32_dec_le(v___x_2423_, v___y_2420_);
if (v___x_2424_ == 0)
{
return v___x_2424_;
}
else
{
uint32_t v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = 70;
v___x_2426_ = lean_uint32_dec_le(v___y_2420_, v___x_2425_);
return v___x_2426_;
}
}
else
{
return v___y_2422_;
}
}
v___jp_2427_:
{
if (v___y_2428_ == 0)
{
uint32_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = 97;
v___x_2430_ = lean_uint32_dec_le(v___x_2429_, v___y_2420_);
if (v___x_2430_ == 0)
{
v___y_2422_ = v___x_2430_;
goto v___jp_2421_;
}
else
{
uint32_t v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = 102;
v___x_2432_ = lean_uint32_dec_le(v___y_2420_, v___x_2431_);
v___y_2422_ = v___x_2432_;
goto v___jp_2421_;
}
}
else
{
return v___y_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2437_){
_start:
{
uint32_t v___y_54__boxed_2438_; uint8_t v_res_2439_; lean_object* v_r_2440_; 
v___y_54__boxed_2438_ = lean_unbox_uint32(v___y_2437_);
lean_dec(v___y_2437_);
v_res_2439_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_54__boxed_2438_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2443_, uint8_t v_includeWhitespace_2444_, lean_object* v_kind_2445_, lean_object* v_c_2446_, lean_object* v_s_2447_){
_start:
{
lean_object* v___f_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v_s_2451_; lean_object* v___x_2452_; 
v___f_2448_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2449_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2450_ = 1;
v_s_2451_ = l_Lean_Parser_takeDigitsFn(v___f_2448_, v___x_2449_, v___x_2450_, v_c_2446_, v_s_2447_);
v___x_2452_ = l_Lean_Parser_mkNodeToken(v_kind_2445_, v_startPos_2443_, v_includeWhitespace_2444_, v_c_2446_, v_s_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2453_, lean_object* v_includeWhitespace_2454_, lean_object* v_kind_2455_, lean_object* v_c_2456_, lean_object* v_s_2457_){
_start:
{
uint8_t v_includeWhitespace_boxed_2458_; lean_object* v_res_2459_; 
v_includeWhitespace_boxed_2458_ = lean_unbox(v_includeWhitespace_2454_);
v_res_2459_ = l_Lean_Parser_hexNumberFn(v_startPos_2453_, v_includeWhitespace_boxed_2458_, v_kind_2455_, v_c_2456_, v_s_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2461_, lean_object* v_c_2462_, lean_object* v_s_2463_){
_start:
{
lean_object* v_pos_2464_; uint8_t v___y_2466_; lean_object* v_toInputContext_2471_; uint8_t v___x_2472_; 
v_pos_2464_ = lean_ctor_get(v_s_2463_, 2);
v_toInputContext_2471_ = lean_ctor_get(v_c_2462_, 0);
v___x_2472_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2471_, v_pos_2464_);
if (v___x_2472_ == 0)
{
lean_object* v_inputString_2473_; uint32_t v_curr_2474_; uint32_t v___x_2475_; uint8_t v___x_2476_; 
v_inputString_2473_ = lean_ctor_get(v_toInputContext_2471_, 0);
v_curr_2474_ = lean_string_utf8_get_fast(v_inputString_2473_, v_pos_2464_);
v___x_2475_ = 48;
v___x_2476_ = lean_uint32_dec_eq(v_curr_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_uint32_dec_le(v___x_2475_, v_curr_2474_);
if (v___x_2477_ == 0)
{
v___y_2466_ = v___x_2477_;
goto v___jp_2465_;
}
else
{
uint32_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = 57;
v___x_2479_ = lean_uint32_dec_le(v_curr_2474_, v___x_2478_);
v___y_2466_ = v___x_2479_;
goto v___jp_2465_;
}
}
else
{
lean_object* v_i_2480_; uint32_t v_curr_2491_; uint32_t v___x_2492_; uint8_t v___x_2493_; 
lean_inc(v_pos_2464_);
v_i_2480_ = lean_string_utf8_next_fast(v_inputString_2473_, v_pos_2464_);
v_curr_2491_ = lean_string_utf8_get(v_inputString_2473_, v_i_2480_);
v___x_2492_ = 98;
v___x_2493_ = lean_uint32_dec_eq(v_curr_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
uint32_t v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = 66;
v___x_2495_ = lean_uint32_dec_eq(v_curr_2491_, v___x_2494_);
if (v___x_2495_ == 0)
{
uint32_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = 111;
v___x_2497_ = lean_uint32_dec_eq(v_curr_2491_, v___x_2496_);
if (v___x_2497_ == 0)
{
uint32_t v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = 79;
v___x_2499_ = lean_uint32_dec_eq(v_curr_2491_, v___x_2498_);
if (v___x_2499_ == 0)
{
uint32_t v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = 120;
v___x_2501_ = lean_uint32_dec_eq(v_curr_2491_, v___x_2500_);
if (v___x_2501_ == 0)
{
uint32_t v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = 88;
v___x_2503_ = lean_uint32_dec_eq(v_curr_2491_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = l_Lean_Parser_ParserState_setPos(v_s_2463_, v_i_2480_);
v___x_2505_ = l_Lean_Parser_decimalNumberFn(v_pos_2464_, v_includeWhitespace_2461_, v_c_2462_, v___x_2504_);
return v___x_2505_;
}
else
{
goto v___jp_2481_;
}
}
else
{
goto v___jp_2481_;
}
}
else
{
goto v___jp_2485_;
}
}
else
{
goto v___jp_2485_;
}
}
else
{
goto v___jp_2488_;
}
}
else
{
goto v___jp_2488_;
}
v___jp_2481_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2483_ = l_Lean_Parser_ParserState_next(v_s_2463_, v_c_2462_, v_i_2480_);
v___x_2484_ = l_Lean_Parser_hexNumberFn(v_pos_2464_, v_includeWhitespace_2461_, v___x_2482_, v_c_2462_, v___x_2483_);
return v___x_2484_;
}
v___jp_2485_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = l_Lean_Parser_ParserState_next(v_s_2463_, v_c_2462_, v_i_2480_);
v___x_2487_ = l_Lean_Parser_octalNumberFn(v_pos_2464_, v_includeWhitespace_2461_, v_c_2462_, v___x_2486_);
return v___x_2487_;
}
v___jp_2488_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = l_Lean_Parser_ParserState_next(v_s_2463_, v_c_2462_, v_i_2480_);
v___x_2490_ = l_Lean_Parser_binNumberFn(v_pos_2464_, v_includeWhitespace_2461_, v_c_2462_, v___x_2489_);
return v___x_2490_;
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v_c_2462_);
v___x_2506_ = lean_box(0);
v___x_2507_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2463_, v___x_2506_);
return v___x_2507_;
}
v___jp_2465_:
{
if (v___y_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_dec_ref(v_c_2462_);
v___x_2467_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2468_ = l_Lean_Parser_ParserState_mkError(v_s_2463_, v___x_2467_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_inc(v_pos_2464_);
v___x_2469_ = l_Lean_Parser_ParserState_next(v_s_2463_, v_c_2462_, v_pos_2464_);
v___x_2470_ = l_Lean_Parser_decimalNumberFn(v_pos_2464_, v_includeWhitespace_2461_, v_c_2462_, v___x_2469_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2508_, lean_object* v_c_2509_, lean_object* v_s_2510_){
_start:
{
uint8_t v_includeWhitespace_boxed_2511_; lean_object* v_res_2512_; 
v_includeWhitespace_boxed_2511_ = lean_unbox(v_includeWhitespace_2508_);
v_res_2512_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2511_, v_c_2509_, v_s_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2513_, lean_object* v_s_2514_){
_start:
{
lean_object* v_toInputContext_2515_; lean_object* v_pos_2516_; lean_object* v_inputString_2517_; uint32_t v_curr_2518_; uint32_t v___x_2519_; uint8_t v___x_2520_; 
v_toInputContext_2515_ = lean_ctor_get(v_c_2513_, 0);
v_pos_2516_ = lean_ctor_get(v_s_2514_, 2);
v_inputString_2517_ = lean_ctor_get(v_toInputContext_2515_, 0);
v_curr_2518_ = lean_string_utf8_get(v_inputString_2517_, v_pos_2516_);
v___x_2519_ = 46;
v___x_2520_ = lean_uint32_dec_eq(v_curr_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
return v___x_2520_;
}
else
{
lean_object* v_i_2521_; uint8_t v___x_2522_; 
v_i_2521_ = lean_string_utf8_next(v_inputString_2517_, v_pos_2516_);
v___x_2522_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2515_, v_i_2521_);
if (v___x_2522_ == 0)
{
uint32_t v_curr_2523_; uint8_t v___y_2525_; uint8_t v___y_2529_; uint32_t v___x_2538_; uint8_t v___x_2539_; 
v_curr_2523_ = lean_string_utf8_get(v_inputString_2517_, v_i_2521_);
lean_dec(v_i_2521_);
v___x_2538_ = 65;
v___x_2539_ = lean_uint32_dec_le(v___x_2538_, v_curr_2523_);
if (v___x_2539_ == 0)
{
goto v___jp_2533_;
}
else
{
uint32_t v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = 90;
v___x_2541_ = lean_uint32_dec_le(v_curr_2523_, v___x_2540_);
if (v___x_2541_ == 0)
{
goto v___jp_2533_;
}
else
{
return v___x_2520_;
}
}
v___jp_2524_:
{
if (v___y_2525_ == 0)
{
uint32_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = 171;
v___x_2527_ = lean_uint32_dec_eq(v_curr_2523_, v___x_2526_);
return v___x_2527_;
}
else
{
return v___x_2520_;
}
}
v___jp_2528_:
{
if (v___y_2529_ == 0)
{
uint32_t v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = 95;
v___x_2531_ = lean_uint32_dec_eq(v_curr_2523_, v___x_2530_);
if (v___x_2531_ == 0)
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Lean_isLetterLike(v_curr_2523_);
v___y_2525_ = v___x_2532_;
goto v___jp_2524_;
}
else
{
v___y_2525_ = v___x_2531_;
goto v___jp_2524_;
}
}
else
{
return v___x_2520_;
}
}
v___jp_2533_:
{
uint32_t v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = 97;
v___x_2535_ = lean_uint32_dec_le(v___x_2534_, v_curr_2523_);
if (v___x_2535_ == 0)
{
v___y_2529_ = v___x_2535_;
goto v___jp_2528_;
}
else
{
uint32_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = 122;
v___x_2537_ = lean_uint32_dec_le(v_curr_2523_, v___x_2536_);
v___y_2529_ = v___x_2537_;
goto v___jp_2528_;
}
}
}
else
{
uint8_t v___x_2542_; 
lean_dec(v_i_2521_);
v___x_2542_ = 0;
return v___x_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2543_, lean_object* v_s_2544_){
_start:
{
uint8_t v_res_2545_; lean_object* v_r_2546_; 
v_res_2545_ = l_Lean_Parser_isIdCont(v_c_2543_, v_s_2544_);
lean_dec_ref(v_s_2544_);
lean_dec_ref(v_c_2543_);
v_r_2546_ = lean_box(v_res_2545_);
return v_r_2546_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2547_, lean_object* v_idStopPos_2548_, lean_object* v_tk_2549_){
_start:
{
if (lean_obj_tag(v_tk_2549_) == 0)
{
uint8_t v___x_2550_; 
v___x_2550_ = 0;
return v___x_2550_;
}
else
{
lean_object* v_val_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_val_2551_ = lean_ctor_get(v_tk_2549_, 0);
v___x_2552_ = lean_nat_sub(v_idStopPos_2548_, v_idStartPos_2547_);
v___x_2553_ = lean_string_utf8_byte_size(v_val_2551_);
v___x_2554_ = lean_nat_dec_le(v___x_2552_, v___x_2553_);
lean_dec(v___x_2552_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2555_, lean_object* v_idStopPos_2556_, lean_object* v_tk_2557_){
_start:
{
uint8_t v_res_2558_; lean_object* v_r_2559_; 
v_res_2558_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2555_, v_idStopPos_2556_, v_tk_2557_);
lean_dec(v_tk_2557_);
lean_dec(v_idStopPos_2556_);
lean_dec(v_idStartPos_2555_);
v_r_2559_ = lean_box(v_res_2558_);
return v_r_2559_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object* v_a_2560_, lean_object* v_as_2561_, size_t v_i_2562_, size_t v_stop_2563_){
_start:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_usize_dec_eq(v_i_2562_, v_stop_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2565_ = lean_array_uget_borrowed(v_as_2561_, v_i_2562_);
v___x_2566_ = lean_string_dec_eq(v_a_2560_, v___x_2565_);
if (v___x_2566_ == 0)
{
size_t v___x_2567_; size_t v___x_2568_; 
v___x_2567_ = ((size_t)1ULL);
v___x_2568_ = lean_usize_add(v_i_2562_, v___x_2567_);
v_i_2562_ = v___x_2568_;
goto _start;
}
else
{
return v___x_2566_;
}
}
else
{
uint8_t v___x_2570_; 
v___x_2570_ = 0;
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object* v_a_2571_, lean_object* v_as_2572_, lean_object* v_i_2573_, lean_object* v_stop_2574_){
_start:
{
size_t v_i_boxed_2575_; size_t v_stop_boxed_2576_; uint8_t v_res_2577_; lean_object* v_r_2578_; 
v_i_boxed_2575_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_stop_boxed_2576_ = lean_unbox_usize(v_stop_2574_);
lean_dec(v_stop_2574_);
v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2571_, v_as_2572_, v_i_boxed_2575_, v_stop_boxed_2576_);
lean_dec_ref(v_as_2572_);
lean_dec_ref(v_a_2571_);
v_r_2578_ = lean_box(v_res_2577_);
return v_r_2578_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_as_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2581_ = lean_unsigned_to_nat(0u);
v___x_2582_ = lean_array_get_size(v_as_2579_);
v___x_2583_ = lean_nat_dec_lt(v___x_2581_, v___x_2582_);
if (v___x_2583_ == 0)
{
return v___x_2583_;
}
else
{
if (v___x_2583_ == 0)
{
return v___x_2583_;
}
else
{
size_t v___x_2584_; size_t v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2582_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2580_, v_as_2579_, v___x_2584_, v___x_2585_);
return v___x_2586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_as_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v_res_2589_; lean_object* v_r_2590_; 
v_res_2589_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2587_, v_a_2588_);
lean_dec_ref(v_a_2588_);
lean_dec_ref(v_as_2587_);
v_r_2590_ = lean_box(v_res_2589_);
return v_r_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2593_, lean_object* v_tk_2594_, lean_object* v_c_2595_, lean_object* v_s_2596_){
_start:
{
if (lean_obj_tag(v_tk_2594_) == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref(v_c_2595_);
v___x_2597_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2598_ = lean_box(0);
v___x_2599_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2596_, v___x_2597_, v_startPos_2593_, v___x_2598_);
return v___x_2599_;
}
else
{
lean_object* v_toCacheableParserContext_2600_; lean_object* v_val_2601_; lean_object* v_toInputContext_2602_; lean_object* v_forbiddenTks_2603_; uint8_t v___x_2604_; 
v_toCacheableParserContext_2600_ = lean_ctor_get(v_c_2595_, 2);
v_val_2601_ = lean_ctor_get(v_tk_2594_, 0);
v_toInputContext_2602_ = lean_ctor_get(v_c_2595_, 0);
lean_inc_ref(v_toInputContext_2602_);
v_forbiddenTks_2603_ = lean_ctor_get(v_toCacheableParserContext_2600_, 3);
v___x_2604_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_2603_, v_val_2601_);
if (v___x_2604_ == 0)
{
lean_object* v_leading_2605_; lean_object* v___x_2606_; lean_object* v_stopPos_2607_; lean_object* v_s_2608_; lean_object* v_s_2609_; lean_object* v___y_2611_; lean_object* v_pos_2615_; lean_object* v_inputString_2616_; lean_object* v_endPos_2617_; uint8_t v___x_2618_; 
lean_inc(v_startPos_2593_);
v_leading_2605_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2595_, v_startPos_2593_);
v___x_2606_ = lean_string_utf8_byte_size(v_val_2601_);
v_stopPos_2607_ = lean_nat_add(v_startPos_2593_, v___x_2606_);
lean_inc(v_stopPos_2607_);
v_s_2608_ = l_Lean_Parser_ParserState_setPos(v_s_2596_, v_stopPos_2607_);
v_s_2609_ = l_Lean_Parser_whitespace(v_c_2595_, v_s_2608_);
v_pos_2615_ = lean_ctor_get(v_s_2609_, 2);
lean_inc(v_pos_2615_);
v_inputString_2616_ = lean_ctor_get(v_toInputContext_2602_, 0);
lean_inc_ref(v_inputString_2616_);
v_endPos_2617_ = lean_ctor_get(v_toInputContext_2602_, 3);
lean_inc(v_endPos_2617_);
lean_dec_ref(v_toInputContext_2602_);
v___x_2618_ = lean_nat_dec_le(v_pos_2615_, v_endPos_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_dec(v_pos_2615_);
lean_inc(v_stopPos_2607_);
v___x_2619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2619_, 0, v_inputString_2616_);
lean_ctor_set(v___x_2619_, 1, v_stopPos_2607_);
lean_ctor_set(v___x_2619_, 2, v_endPos_2617_);
v___y_2611_ = v___x_2619_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2620_; 
lean_dec(v_endPos_2617_);
lean_inc(v_stopPos_2607_);
v___x_2620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2620_, 0, v_inputString_2616_);
lean_ctor_set(v___x_2620_, 1, v_stopPos_2607_);
lean_ctor_set(v___x_2620_, 2, v_pos_2615_);
v___y_2611_ = v___x_2620_;
goto v___jp_2610_;
}
v___jp_2610_:
{
lean_object* v___x_2612_; lean_object* v_atom_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2612_, 0, v_leading_2605_);
lean_ctor_set(v___x_2612_, 1, v_startPos_2593_);
lean_ctor_set(v___x_2612_, 2, v___y_2611_);
lean_ctor_set(v___x_2612_, 3, v_stopPos_2607_);
lean_inc(v_val_2601_);
v_atom_2613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2613_, 0, v___x_2612_);
lean_ctor_set(v_atom_2613_, 1, v_val_2601_);
v___x_2614_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2609_, v_atom_2613_);
return v___x_2614_;
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec_ref(v_toInputContext_2602_);
lean_dec_ref(v_c_2595_);
v___x_2621_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2622_ = lean_box(0);
v___x_2623_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2596_, v___x_2621_, v_startPos_2593_, v___x_2622_);
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2624_, lean_object* v_tk_2625_, lean_object* v_c_2626_, lean_object* v_s_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2624_, v_tk_2625_, v_c_2626_, v_s_2627_);
lean_dec(v_tk_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2629_, lean_object* v_tk_2630_, lean_object* v_val_2631_, uint8_t v_includeWhitespace_2632_, lean_object* v_c_2633_, lean_object* v_s_2634_){
_start:
{
lean_object* v_pos_2635_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; uint8_t v___x_2645_; 
v_pos_2635_ = lean_ctor_get(v_s_2634_, 2);
v___x_2645_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2629_, v_pos_2635_, v_tk_2630_);
if (v___x_2645_ == 0)
{
lean_object* v_toInputContext_2646_; lean_object* v_inputString_2647_; lean_object* v_endPos_2648_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v_pos_2652_; lean_object* v___y_2658_; uint8_t v___x_2661_; 
lean_inc(v_pos_2635_);
v_toInputContext_2646_ = lean_ctor_get(v_c_2633_, 0);
v_inputString_2647_ = lean_ctor_get(v_toInputContext_2646_, 0);
lean_inc_ref(v_inputString_2647_);
v_endPos_2648_ = lean_ctor_get(v_toInputContext_2646_, 3);
lean_inc(v_endPos_2648_);
v___x_2661_ = lean_nat_dec_le(v_pos_2635_, v_endPos_2648_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_inc(v_endPos_2648_);
lean_inc(v_startPos_2629_);
lean_inc_ref(v_inputString_2647_);
v___x_2662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2662_, 0, v_inputString_2647_);
lean_ctor_set(v___x_2662_, 1, v_startPos_2629_);
lean_ctor_set(v___x_2662_, 2, v_endPos_2648_);
v___y_2658_ = v___x_2662_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2663_; 
lean_inc(v_pos_2635_);
lean_inc(v_startPos_2629_);
lean_inc_ref(v_inputString_2647_);
v___x_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2663_, 0, v_inputString_2647_);
lean_ctor_set(v___x_2663_, 1, v_startPos_2629_);
lean_ctor_set(v___x_2663_, 2, v_pos_2635_);
v___y_2658_ = v___x_2663_;
goto v___jp_2657_;
}
v___jp_2649_:
{
lean_object* v_leading_2653_; uint8_t v___x_2654_; 
lean_inc(v_startPos_2629_);
v_leading_2653_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2633_, v_startPos_2629_);
lean_dec_ref(v_c_2633_);
v___x_2654_ = lean_nat_dec_le(v_pos_2652_, v_endPos_2648_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec(v_pos_2652_);
lean_inc(v_pos_2635_);
v___x_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2655_, 0, v_inputString_2647_);
lean_ctor_set(v___x_2655_, 1, v_pos_2635_);
lean_ctor_set(v___x_2655_, 2, v_endPos_2648_);
v___y_2637_ = v___y_2650_;
v___y_2638_ = v_leading_2653_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___x_2655_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2656_; 
lean_dec(v_endPos_2648_);
lean_inc(v_pos_2635_);
v___x_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2656_, 0, v_inputString_2647_);
lean_ctor_set(v___x_2656_, 1, v_pos_2635_);
lean_ctor_set(v___x_2656_, 2, v_pos_2652_);
v___y_2637_ = v___y_2650_;
v___y_2638_ = v_leading_2653_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___x_2656_;
goto v___jp_2636_;
}
}
v___jp_2657_:
{
if (v_includeWhitespace_2632_ == 0)
{
lean_inc(v_pos_2635_);
v___y_2650_ = v___y_2658_;
v___y_2651_ = v_s_2634_;
v_pos_2652_ = v_pos_2635_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2659_; lean_object* v_pos_2660_; 
lean_inc_ref(v_c_2633_);
v___x_2659_ = l_Lean_Parser_whitespace(v_c_2633_, v_s_2634_);
v_pos_2660_ = lean_ctor_get(v___x_2659_, 2);
lean_inc(v_pos_2660_);
v___y_2650_ = v___y_2658_;
v___y_2651_ = v___x_2659_;
v_pos_2652_ = v_pos_2660_;
goto v___jp_2649_;
}
}
}
else
{
lean_object* v___x_2664_; 
lean_dec(v_val_2631_);
v___x_2664_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2629_, v_tk_2630_, v_c_2633_, v_s_2634_);
return v___x_2664_;
}
v___jp_2636_:
{
lean_object* v_info_2641_; lean_object* v___x_2642_; lean_object* v_atom_2643_; lean_object* v___x_2644_; 
v_info_2641_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2641_, 0, v___y_2638_);
lean_ctor_set(v_info_2641_, 1, v_startPos_2629_);
lean_ctor_set(v_info_2641_, 2, v___y_2640_);
lean_ctor_set(v_info_2641_, 3, v_pos_2635_);
v___x_2642_ = lean_box(0);
v_atom_2643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2643_, 0, v_info_2641_);
lean_ctor_set(v_atom_2643_, 1, v___y_2637_);
lean_ctor_set(v_atom_2643_, 2, v_val_2631_);
lean_ctor_set(v_atom_2643_, 3, v___x_2642_);
v___x_2644_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2639_, v_atom_2643_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2665_, lean_object* v_tk_2666_, lean_object* v_val_2667_, lean_object* v_includeWhitespace_2668_, lean_object* v_c_2669_, lean_object* v_s_2670_){
_start:
{
uint8_t v_includeWhitespace_boxed_2671_; lean_object* v_res_2672_; 
v_includeWhitespace_boxed_2671_ = lean_unbox(v_includeWhitespace_2668_);
v_res_2672_ = l_Lean_Parser_mkIdResult(v_startPos_2665_, v_tk_2666_, v_val_2667_, v_includeWhitespace_boxed_2671_, v_c_2669_, v_s_2670_);
lean_dec(v_tk_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2673_){
_start:
{
uint8_t v___y_2675_; uint8_t v___y_2687_; uint32_t v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = 65;
v___x_2698_ = lean_uint32_dec_le(v___x_2697_, v___y_2673_);
if (v___x_2698_ == 0)
{
goto v___jp_2692_;
}
else
{
uint32_t v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = 90;
v___x_2700_ = lean_uint32_dec_le(v___y_2673_, v___x_2699_);
if (v___x_2700_ == 0)
{
goto v___jp_2692_;
}
else
{
return v___x_2700_;
}
}
v___jp_2674_:
{
if (v___y_2675_ == 0)
{
uint32_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = 95;
v___x_2677_ = lean_uint32_dec_eq(v___y_2673_, v___x_2676_);
if (v___x_2677_ == 0)
{
uint32_t v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = 39;
v___x_2679_ = lean_uint32_dec_eq(v___y_2673_, v___x_2678_);
if (v___x_2679_ == 0)
{
uint32_t v___x_2680_; uint8_t v___x_2681_; 
v___x_2680_ = 33;
v___x_2681_ = lean_uint32_dec_eq(v___y_2673_, v___x_2680_);
if (v___x_2681_ == 0)
{
uint32_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = 63;
v___x_2683_ = lean_uint32_dec_eq(v___y_2673_, v___x_2682_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
v___x_2684_ = l_Lean_isLetterLike(v___y_2673_);
if (v___x_2684_ == 0)
{
uint8_t v___x_2685_; 
v___x_2685_ = l_Lean_isSubScriptAlnum(v___y_2673_);
return v___x_2685_;
}
else
{
return v___x_2684_;
}
}
else
{
return v___x_2683_;
}
}
else
{
return v___x_2681_;
}
}
else
{
return v___x_2679_;
}
}
else
{
return v___x_2677_;
}
}
else
{
return v___y_2675_;
}
}
v___jp_2686_:
{
if (v___y_2687_ == 0)
{
uint32_t v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = 48;
v___x_2689_ = lean_uint32_dec_le(v___x_2688_, v___y_2673_);
if (v___x_2689_ == 0)
{
v___y_2675_ = v___x_2689_;
goto v___jp_2674_;
}
else
{
uint32_t v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = 57;
v___x_2691_ = lean_uint32_dec_le(v___y_2673_, v___x_2690_);
v___y_2675_ = v___x_2691_;
goto v___jp_2674_;
}
}
else
{
return v___y_2687_;
}
}
v___jp_2692_:
{
uint32_t v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = 97;
v___x_2694_ = lean_uint32_dec_le(v___x_2693_, v___y_2673_);
if (v___x_2694_ == 0)
{
v___y_2687_ = v___x_2694_;
goto v___jp_2686_;
}
else
{
uint32_t v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = 122;
v___x_2696_ = lean_uint32_dec_le(v___y_2673_, v___x_2695_);
v___y_2687_ = v___x_2696_;
goto v___jp_2686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2701_){
_start:
{
uint32_t v___y_633__boxed_2702_; uint8_t v_res_2703_; lean_object* v_r_2704_; 
v___y_633__boxed_2702_ = lean_unbox_uint32(v___y_2701_);
lean_dec(v___y_2701_);
v_res_2703_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_633__boxed_2702_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2705_){
_start:
{
uint32_t v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = 187;
v___x_2707_ = lean_uint32_dec_eq(v___y_2705_, v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2708_){
_start:
{
uint32_t v___y_690__boxed_2709_; uint8_t v_res_2710_; lean_object* v_r_2711_; 
v___y_690__boxed_2709_ = lean_unbox_uint32(v___y_2708_);
lean_dec(v___y_2708_);
v_res_2710_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_690__boxed_2709_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2715_, lean_object* v_tk_2716_, uint8_t v_includeWhitespace_2717_, lean_object* v_r_2718_, lean_object* v_c_2719_, lean_object* v_s_2720_){
_start:
{
lean_object* v_pos_2721_; lean_object* v_toInputContext_2722_; uint8_t v___x_2723_; 
v_pos_2721_ = lean_ctor_get(v_s_2720_, 2);
v_toInputContext_2722_ = lean_ctor_get(v_c_2719_, 0);
v___x_2723_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2722_, v_pos_2721_);
if (v___x_2723_ == 0)
{
lean_object* v_inputString_2724_; uint32_t v_curr_2725_; uint32_t v___x_2726_; uint8_t v___x_2727_; 
v_inputString_2724_ = lean_ctor_get(v_toInputContext_2722_, 0);
v_curr_2725_ = lean_string_utf8_get_fast(v_inputString_2724_, v_pos_2721_);
v___x_2726_ = 171;
v___x_2727_ = lean_uint32_dec_eq(v_curr_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___f_2728_; uint8_t v___y_2740_; uint8_t v___y_2743_; uint32_t v___x_2752_; uint8_t v___x_2753_; 
v___f_2728_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2752_ = 65;
v___x_2753_ = lean_uint32_dec_le(v___x_2752_, v_curr_2725_);
if (v___x_2753_ == 0)
{
goto v___jp_2747_;
}
else
{
uint32_t v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = 90;
v___x_2755_ = lean_uint32_dec_le(v_curr_2725_, v___x_2754_);
if (v___x_2755_ == 0)
{
goto v___jp_2747_;
}
else
{
lean_inc(v_pos_2721_);
goto v___jp_2729_;
}
}
v___jp_2729_:
{
lean_object* v___x_2730_; lean_object* v_s_2731_; lean_object* v_pos_2732_; lean_object* v___x_2733_; lean_object* v_r_2734_; uint8_t v___x_2735_; 
v___x_2730_ = l_Lean_Parser_ParserState_next(v_s_2720_, v_c_2719_, v_pos_2721_);
v_s_2731_ = l_Lean_Parser_takeWhileFn(v___f_2728_, v_c_2719_, v___x_2730_);
v_pos_2732_ = lean_ctor_get(v_s_2731_, 2);
lean_inc(v_pos_2732_);
v___x_2733_ = lean_string_utf8_extract(v_inputString_2724_, v_pos_2721_, v_pos_2732_);
lean_dec(v_pos_2721_);
v_r_2734_ = l_Lean_Name_str___override(v_r_2718_, v___x_2733_);
v___x_2735_ = l_Lean_Parser_isIdCont(v_c_2719_, v_s_2731_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; 
lean_dec(v_pos_2732_);
v___x_2736_ = l_Lean_Parser_mkIdResult(v_startPos_2715_, v_tk_2716_, v_r_2734_, v_includeWhitespace_2717_, v_c_2719_, v_s_2731_);
return v___x_2736_;
}
else
{
lean_object* v_s_2737_; 
v_s_2737_ = l_Lean_Parser_ParserState_next(v_s_2731_, v_c_2719_, v_pos_2732_);
lean_dec(v_pos_2732_);
v_r_2718_ = v_r_2734_;
v_s_2720_ = v_s_2737_;
goto _start;
}
}
v___jp_2739_:
{
if (v___y_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_dec(v_r_2718_);
v___x_2741_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2715_, v_tk_2716_, v_c_2719_, v_s_2720_);
return v___x_2741_;
}
else
{
lean_inc(v_pos_2721_);
goto v___jp_2729_;
}
}
v___jp_2742_:
{
if (v___y_2743_ == 0)
{
uint32_t v___x_2744_; uint8_t v___x_2745_; 
v___x_2744_ = 95;
v___x_2745_ = lean_uint32_dec_eq(v_curr_2725_, v___x_2744_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
v___x_2746_ = l_Lean_isLetterLike(v_curr_2725_);
v___y_2740_ = v___x_2746_;
goto v___jp_2739_;
}
else
{
v___y_2740_ = v___x_2745_;
goto v___jp_2739_;
}
}
else
{
lean_inc(v_pos_2721_);
goto v___jp_2729_;
}
}
v___jp_2747_:
{
uint32_t v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = 97;
v___x_2749_ = lean_uint32_dec_le(v___x_2748_, v_curr_2725_);
if (v___x_2749_ == 0)
{
v___y_2743_ = v___x_2749_;
goto v___jp_2742_;
}
else
{
uint32_t v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = 122;
v___x_2751_ = lean_uint32_dec_le(v_curr_2725_, v___x_2750_);
v___y_2743_ = v___x_2751_;
goto v___jp_2742_;
}
}
}
else
{
lean_object* v___f_2756_; lean_object* v_startPart_2757_; lean_object* v___x_2758_; lean_object* v_s_2759_; lean_object* v_pos_2760_; uint8_t v___x_2761_; 
v___f_2756_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2757_ = lean_string_utf8_next_fast(v_inputString_2724_, v_pos_2721_);
v___x_2758_ = l_Lean_Parser_ParserState_setPos(v_s_2720_, v_startPart_2757_);
v_s_2759_ = l_Lean_Parser_takeUntilFn(v___f_2756_, v_c_2719_, v___x_2758_);
v_pos_2760_ = lean_ctor_get(v_s_2759_, 2);
lean_inc(v_pos_2760_);
v___x_2761_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2722_, v_pos_2760_);
if (v___x_2761_ == 0)
{
lean_object* v_s_2762_; lean_object* v___x_2763_; lean_object* v_r_2764_; uint8_t v___x_2765_; 
v_s_2762_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2759_, v_c_2719_, v_pos_2760_);
v___x_2763_ = lean_string_utf8_extract(v_inputString_2724_, v_startPart_2757_, v_pos_2760_);
lean_dec(v_pos_2760_);
v_r_2764_ = l_Lean_Name_str___override(v_r_2718_, v___x_2763_);
v___x_2765_ = l_Lean_Parser_isIdCont(v_c_2719_, v_s_2762_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Parser_mkIdResult(v_startPos_2715_, v_tk_2716_, v_r_2764_, v_includeWhitespace_2717_, v_c_2719_, v_s_2762_);
return v___x_2766_;
}
else
{
lean_object* v_pos_2767_; lean_object* v_s_2768_; 
v_pos_2767_ = lean_ctor_get(v_s_2762_, 2);
lean_inc(v_pos_2767_);
v_s_2768_ = l_Lean_Parser_ParserState_next(v_s_2762_, v_c_2719_, v_pos_2767_);
lean_dec(v_pos_2767_);
v_r_2718_ = v_r_2764_;
v_s_2720_ = v_s_2768_;
goto _start;
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v_pos_2760_);
lean_dec_ref(v_c_2719_);
lean_dec(v_r_2718_);
lean_dec(v_startPos_2715_);
v___x_2770_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2771_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2759_, v___x_2770_, v_startPart_2757_);
return v___x_2771_;
}
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec_ref(v_c_2719_);
lean_dec(v_r_2718_);
lean_dec(v_startPos_2715_);
v___x_2772_ = lean_box(0);
v___x_2773_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2720_, v___x_2772_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2774_, lean_object* v_tk_2775_, lean_object* v_includeWhitespace_2776_, lean_object* v_r_2777_, lean_object* v_c_2778_, lean_object* v_s_2779_){
_start:
{
uint8_t v_includeWhitespace_boxed_2780_; lean_object* v_res_2781_; 
v_includeWhitespace_boxed_2780_ = lean_unbox(v_includeWhitespace_2776_);
v_res_2781_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2774_, v_tk_2775_, v_includeWhitespace_boxed_2780_, v_r_2777_, v_c_2778_, v_s_2779_);
lean_dec(v_tk_2775_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2782_, lean_object* v_tk_2783_, lean_object* v_r_2784_, uint8_t v_includeWhitespace_2785_, lean_object* v_c_2786_, lean_object* v_s_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2782_, v_tk_2783_, v_includeWhitespace_2785_, v_r_2784_, v_c_2786_, v_s_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2789_, lean_object* v_tk_2790_, lean_object* v_r_2791_, lean_object* v_includeWhitespace_2792_, lean_object* v_c_2793_, lean_object* v_s_2794_){
_start:
{
uint8_t v_includeWhitespace_boxed_2795_; lean_object* v_res_2796_; 
v_includeWhitespace_boxed_2795_ = lean_unbox(v_includeWhitespace_2792_);
v_res_2796_ = l_Lean_Parser_identFnAux(v_startPos_2789_, v_tk_2790_, v_r_2791_, v_includeWhitespace_boxed_2795_, v_c_2793_, v_s_2794_);
lean_dec(v_tk_2790_);
return v_res_2796_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2797_){
_start:
{
uint8_t v___y_2799_; uint8_t v___y_2803_; uint32_t v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = 65;
v___x_2813_ = lean_uint32_dec_le(v___x_2812_, v_c_2797_);
if (v___x_2813_ == 0)
{
goto v___jp_2807_;
}
else
{
uint32_t v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = 90;
v___x_2815_ = lean_uint32_dec_le(v_c_2797_, v___x_2814_);
if (v___x_2815_ == 0)
{
goto v___jp_2807_;
}
else
{
return v___x_2815_;
}
}
v___jp_2798_:
{
if (v___y_2799_ == 0)
{
uint32_t v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = 171;
v___x_2801_ = lean_uint32_dec_eq(v_c_2797_, v___x_2800_);
return v___x_2801_;
}
else
{
return v___y_2799_;
}
}
v___jp_2802_:
{
if (v___y_2803_ == 0)
{
uint32_t v___x_2804_; uint8_t v___x_2805_; 
v___x_2804_ = 95;
v___x_2805_ = lean_uint32_dec_eq(v_c_2797_, v___x_2804_);
if (v___x_2805_ == 0)
{
uint8_t v___x_2806_; 
v___x_2806_ = l_Lean_isLetterLike(v_c_2797_);
v___y_2799_ = v___x_2806_;
goto v___jp_2798_;
}
else
{
v___y_2799_ = v___x_2805_;
goto v___jp_2798_;
}
}
else
{
return v___y_2803_;
}
}
v___jp_2807_:
{
uint32_t v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = 97;
v___x_2809_ = lean_uint32_dec_le(v___x_2808_, v_c_2797_);
if (v___x_2809_ == 0)
{
v___y_2803_ = v___x_2809_;
goto v___jp_2802_;
}
else
{
uint32_t v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = 122;
v___x_2811_ = lean_uint32_dec_le(v_c_2797_, v___x_2810_);
v___y_2803_ = v___x_2811_;
goto v___jp_2802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2816_){
_start:
{
uint32_t v_c_boxed_2817_; uint8_t v_res_2818_; lean_object* v_r_2819_; 
v_c_boxed_2817_ = lean_unbox_uint32(v_c_2816_);
lean_dec(v_c_2816_);
v_res_2818_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2817_);
v_r_2819_ = lean_box(v_res_2818_);
return v_r_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2821_, lean_object* v_c_2822_, lean_object* v_s_2823_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; lean_object* v_s_2828_; lean_object* v_stxStack_2829_; lean_object* v_errorMsg_2830_; uint8_t v___x_2831_; 
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_box(0);
v___x_2826_ = 1;
v___x_2827_ = l_Lean_Parser_ParserState_next(v_s_2823_, v_c_2822_, v_startPos_2821_);
v_s_2828_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2821_, v___x_2824_, v___x_2826_, v___x_2825_, v_c_2822_, v___x_2827_);
v_stxStack_2829_ = lean_ctor_get(v_s_2828_, 0);
lean_inc_ref(v_stxStack_2829_);
v_errorMsg_2830_ = lean_ctor_get(v_s_2828_, 4);
lean_inc(v_errorMsg_2830_);
v___x_2831_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2830_, v___x_2824_);
lean_dec(v_errorMsg_2830_);
if (v___x_2831_ == 0)
{
lean_dec_ref(v_stxStack_2829_);
return v_s_2828_;
}
else
{
lean_object* v_stx_2832_; 
v_stx_2832_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2829_);
lean_dec_ref(v_stxStack_2829_);
if (lean_obj_tag(v_stx_2832_) == 3)
{
lean_object* v_rawVal_2833_; lean_object* v_info_2834_; lean_object* v_str_2835_; lean_object* v_startPos_2836_; lean_object* v_stopPos_2837_; lean_object* v_s_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_rawVal_2833_ = lean_ctor_get(v_stx_2832_, 1);
lean_inc_ref(v_rawVal_2833_);
v_info_2834_ = lean_ctor_get(v_stx_2832_, 0);
lean_inc(v_info_2834_);
lean_dec_ref_known(v_stx_2832_, 4);
v_str_2835_ = lean_ctor_get(v_rawVal_2833_, 0);
lean_inc_ref(v_str_2835_);
v_startPos_2836_ = lean_ctor_get(v_rawVal_2833_, 1);
lean_inc(v_startPos_2836_);
v_stopPos_2837_ = lean_ctor_get(v_rawVal_2833_, 2);
lean_inc(v_stopPos_2837_);
lean_dec_ref(v_rawVal_2833_);
v_s_2838_ = l_Lean_Parser_ParserState_popSyntax(v_s_2828_);
v___x_2839_ = lean_string_utf8_extract(v_str_2835_, v_startPos_2836_, v_stopPos_2837_);
lean_dec(v_stopPos_2837_);
lean_dec(v_startPos_2836_);
lean_dec_ref(v_str_2835_);
v___x_2840_ = l_Lean_Syntax_mkNameLit(v___x_2839_, v_info_2834_);
v___x_2841_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2838_, v___x_2840_);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec(v_stx_2832_);
v___x_2842_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2843_ = l_Lean_Parser_ParserState_mkError(v_s_2828_, v___x_2842_);
return v___x_2843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2844_, lean_object* v_s_2845_){
_start:
{
lean_object* v_toInputContext_2846_; lean_object* v_pos_2847_; lean_object* v_tokens_2848_; lean_object* v_inputString_2849_; lean_object* v_endPos_2850_; uint32_t v_curr_2851_; uint32_t v___x_2852_; uint8_t v___x_2853_; uint8_t v___x_2854_; uint8_t v___y_2856_; uint8_t v___y_2863_; uint8_t v___y_2870_; uint8_t v___y_2878_; 
v_toInputContext_2846_ = lean_ctor_get(v_c_2844_, 0);
v_pos_2847_ = lean_ctor_get(v_s_2845_, 2);
v_tokens_2848_ = lean_ctor_get(v_c_2844_, 3);
v_inputString_2849_ = lean_ctor_get(v_toInputContext_2846_, 0);
v_endPos_2850_ = lean_ctor_get(v_toInputContext_2846_, 3);
v_curr_2851_ = lean_string_utf8_get(v_inputString_2849_, v_pos_2847_);
v___x_2852_ = 34;
v___x_2853_ = lean_uint32_dec_eq(v_curr_2851_, v___x_2852_);
v___x_2854_ = 1;
if (v___x_2853_ == 0)
{
uint32_t v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = 39;
v___x_2886_ = lean_uint32_dec_eq(v_curr_2851_, v___x_2885_);
if (v___x_2886_ == 0)
{
v___y_2878_ = v___x_2886_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2887_; uint32_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_string_utf8_next(v_inputString_2849_, v_pos_2847_);
v___x_2888_ = lean_string_utf8_get(v_inputString_2849_, v___x_2887_);
lean_dec(v___x_2887_);
v___x_2889_ = lean_uint32_dec_eq(v___x_2888_, v___x_2885_);
if (v___x_2889_ == 0)
{
v___y_2878_ = v___x_2886_;
goto v___jp_2877_;
}
else
{
v___y_2878_ = v___x_2853_;
goto v___jp_2877_;
}
}
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_inc(v_pos_2847_);
v___x_2890_ = l_Lean_Parser_ParserState_next(v_s_2845_, v_c_2844_, v_pos_2847_);
v___x_2891_ = l_Lean_Parser_strLitFnAux(v_pos_2847_, v___x_2854_, v_c_2844_, v___x_2890_);
return v___x_2891_;
}
v___jp_2855_:
{
if (v___y_2856_ == 0)
{
lean_object* v_tk_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_inc(v_pos_2847_);
v_tk_2857_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2849_, v_tokens_2848_, v_pos_2847_, v_endPos_2850_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2847_, v_tk_2857_, v___x_2854_, v___x_2858_, v_c_2844_, v_s_2845_);
lean_dec(v_tk_2857_);
return v___x_2859_;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = l_Lean_Parser_ParserState_next(v_s_2845_, v_c_2844_, v_pos_2847_);
v___x_2861_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2847_, v_c_2844_, v___x_2860_);
return v___x_2861_;
}
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
uint32_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = 114;
v___x_2865_ = lean_uint32_dec_eq(v_curr_2851_, v___x_2864_);
if (v___x_2865_ == 0)
{
v___y_2856_ = v___x_2865_;
goto v___jp_2855_;
}
else
{
lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2866_ = lean_string_utf8_next(v_inputString_2849_, v_pos_2847_);
v___x_2867_ = l_Lean_Parser_isRawStrLitStart(v_c_2844_, v___x_2866_);
v___y_2856_ = v___x_2867_;
goto v___jp_2855_;
}
}
else
{
lean_object* v___x_2868_; 
v___x_2868_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2847_, v_c_2844_, v_s_2845_);
return v___x_2868_;
}
}
v___jp_2869_:
{
if (v___y_2870_ == 0)
{
uint32_t v___x_2871_; uint8_t v___x_2872_; 
lean_inc(v_pos_2847_);
v___x_2871_ = 96;
v___x_2872_ = lean_uint32_dec_eq(v_curr_2851_, v___x_2871_);
if (v___x_2872_ == 0)
{
v___y_2863_ = v___x_2872_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2873_; uint32_t v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = lean_string_utf8_next(v_inputString_2849_, v_pos_2847_);
v___x_2874_ = lean_string_utf8_get(v_inputString_2849_, v___x_2873_);
lean_dec(v___x_2873_);
v___x_2875_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2874_);
v___y_2863_ = v___x_2875_;
goto v___jp_2862_;
}
}
else
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Parser_numberFnAux(v___x_2854_, v_c_2844_, v_s_2845_);
return v___x_2876_;
}
}
v___jp_2877_:
{
if (v___y_2878_ == 0)
{
uint32_t v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = 48;
v___x_2880_ = lean_uint32_dec_le(v___x_2879_, v_curr_2851_);
if (v___x_2880_ == 0)
{
v___y_2870_ = v___x_2880_;
goto v___jp_2869_;
}
else
{
uint32_t v___x_2881_; uint8_t v___x_2882_; 
v___x_2881_ = 57;
v___x_2882_ = lean_uint32_dec_le(v_curr_2851_, v___x_2881_);
v___y_2870_ = v___x_2882_;
goto v___jp_2869_;
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc(v_pos_2847_);
v___x_2883_ = l_Lean_Parser_ParserState_next(v_s_2845_, v_c_2844_, v_pos_2847_);
v___x_2884_ = l_Lean_Parser_charLitFnAux(v_pos_2847_, v_c_2844_, v___x_2883_);
return v___x_2884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2892_, lean_object* v_s_2893_){
_start:
{
lean_object* v_cache_2894_; lean_object* v_errorMsg_2895_; 
v_cache_2894_ = lean_ctor_get(v_s_2893_, 3);
lean_inc_ref(v_cache_2894_);
v_errorMsg_2895_ = lean_ctor_get(v_s_2893_, 4);
if (lean_obj_tag(v_errorMsg_2895_) == 0)
{
lean_object* v_stxStack_2896_; lean_object* v_lhsPrec_2897_; lean_object* v_pos_2898_; lean_object* v_recoveredErrors_2899_; lean_object* v_parserCache_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2925_; 
v_stxStack_2896_ = lean_ctor_get(v_s_2893_, 0);
v_lhsPrec_2897_ = lean_ctor_get(v_s_2893_, 1);
v_pos_2898_ = lean_ctor_get(v_s_2893_, 2);
v_recoveredErrors_2899_ = lean_ctor_get(v_s_2893_, 5);
v_parserCache_2900_ = lean_ctor_get(v_cache_2894_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_cache_2894_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v_cache_2894_, 0);
lean_dec(v_unused_2926_);
v___x_2902_ = v_cache_2894_;
v_isShared_2903_ = v_isSharedCheck_2925_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_parserCache_2900_);
lean_dec(v_cache_2894_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2925_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2904_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2896_);
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_nat_dec_eq(v___x_2904_, v___x_2905_);
lean_dec(v___x_2904_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2918_; 
lean_inc_ref(v_recoveredErrors_2899_);
lean_inc(v_pos_2898_);
lean_inc(v_lhsPrec_2897_);
lean_inc_ref(v_stxStack_2896_);
lean_inc(v_errorMsg_2895_);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_s_2893_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; 
v_unused_2919_ = lean_ctor_get(v_s_2893_, 5);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_s_2893_, 4);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_s_2893_, 3);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_s_2893_, 2);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_s_2893_, 1);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_s_2893_, 0);
lean_dec(v_unused_2924_);
v___x_2908_ = v_s_2893_;
v_isShared_2909_ = v_isSharedCheck_2918_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v_s_2893_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2918_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v_tk_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v_tk_2910_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2896_);
lean_inc(v_pos_2898_);
v___x_2911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2911_, 0, v_startPos_2892_);
lean_ctor_set(v___x_2911_, 1, v_pos_2898_);
lean_ctor_set(v___x_2911_, 2, v_tk_2910_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2911_);
v___x_2913_ = v___x_2902_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_parserCache_2900_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2915_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 3, v___x_2913_);
v___x_2915_ = v___x_2908_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_stxStack_2896_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_lhsPrec_2897_);
lean_ctor_set(v_reuseFailAlloc_2916_, 2, v_pos_2898_);
lean_ctor_set(v_reuseFailAlloc_2916_, 3, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2916_, 4, v_errorMsg_2895_);
lean_ctor_set(v_reuseFailAlloc_2916_, 5, v_recoveredErrors_2899_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_del_object(v___x_2902_);
lean_dec_ref(v_parserCache_2900_);
lean_dec(v_startPos_2892_);
return v_s_2893_;
}
}
}
else
{
lean_dec_ref(v_cache_2894_);
lean_dec(v_startPos_2892_);
return v_s_2893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2927_, lean_object* v_c_2928_, lean_object* v_s_2929_){
_start:
{
lean_object* v_pos_2930_; lean_object* v_cache_2931_; lean_object* v_toInputContext_2932_; uint8_t v___x_2933_; 
v_pos_2930_ = lean_ctor_get(v_s_2929_, 2);
v_cache_2931_ = lean_ctor_get(v_s_2929_, 3);
v_toInputContext_2932_ = lean_ctor_get(v_c_2928_, 0);
v___x_2933_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2932_, v_pos_2930_);
if (v___x_2933_ == 0)
{
lean_object* v_tokenCache_2934_; lean_object* v_startPos_2935_; lean_object* v_stopPos_2936_; lean_object* v_token_2937_; uint8_t v___x_2938_; 
lean_dec(v_expected_2927_);
v_tokenCache_2934_ = lean_ctor_get(v_cache_2931_, 0);
v_startPos_2935_ = lean_ctor_get(v_tokenCache_2934_, 0);
v_stopPos_2936_ = lean_ctor_get(v_tokenCache_2934_, 1);
v_token_2937_ = lean_ctor_get(v_tokenCache_2934_, 2);
v___x_2938_ = lean_nat_dec_eq(v_startPos_2935_, v_pos_2930_);
if (v___x_2938_ == 0)
{
lean_object* v_s_2939_; lean_object* v___x_2940_; 
lean_inc(v_pos_2930_);
v_s_2939_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2928_, v_s_2929_);
v___x_2940_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2930_, v_s_2939_);
return v___x_2940_;
}
else
{
lean_object* v_s_2941_; lean_object* v___x_2942_; 
lean_inc(v_token_2937_);
lean_inc(v_stopPos_2936_);
lean_dec_ref(v_c_2928_);
v_s_2941_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2929_, v_token_2937_);
v___x_2942_ = l_Lean_Parser_ParserState_setPos(v_s_2941_, v_stopPos_2936_);
return v___x_2942_;
}
}
else
{
lean_object* v___x_2943_; 
lean_dec_ref(v_c_2928_);
v___x_2943_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2929_, v_expected_2927_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2944_, lean_object* v_s_2945_){
_start:
{
lean_object* v_pos_2946_; lean_object* v_iniSz_2947_; lean_object* v___x_2948_; lean_object* v_s_2949_; lean_object* v_errorMsg_2950_; 
v_pos_2946_ = lean_ctor_get(v_s_2945_, 2);
lean_inc(v_pos_2946_);
v_iniSz_2947_ = l_Lean_Parser_ParserState_stackSize(v_s_2945_);
v___x_2948_ = lean_box(0);
v_s_2949_ = l_Lean_Parser_tokenFn(v___x_2948_, v_c_2944_, v_s_2945_);
v_errorMsg_2950_ = lean_ctor_get(v_s_2949_, 4);
lean_inc(v_errorMsg_2950_);
if (lean_obj_tag(v_errorMsg_2950_) == 1)
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2959_; 
v_isSharedCheck_2959_ = !lean_is_exclusive(v_errorMsg_2950_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v_errorMsg_2950_, 0);
lean_dec(v_unused_2960_);
v___x_2952_ = v_errorMsg_2950_;
v_isShared_2953_ = v_isSharedCheck_2959_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_errorMsg_2950_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2959_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_inc_ref(v_s_2949_);
v___x_2954_ = l_Lean_Parser_ParserState_restore(v_s_2949_, v_iniSz_2947_, v_pos_2946_);
lean_dec(v_iniSz_2947_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 0);
lean_ctor_set(v___x_2952_, 0, v_s_2949_);
v___x_2956_ = v___x_2952_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_s_2949_);
v___x_2956_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2954_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
return v___x_2957_;
}
}
}
else
{
lean_object* v_stxStack_2961_; lean_object* v_stx_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_errorMsg_2950_);
v_stxStack_2961_ = lean_ctor_get(v_s_2949_, 0);
lean_inc_ref(v_stxStack_2961_);
v_stx_2962_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2961_);
lean_dec_ref(v_stxStack_2961_);
v___x_2963_ = l_Lean_Parser_ParserState_restore(v_s_2949_, v_iniSz_2947_, v_pos_2946_);
lean_dec(v_iniSz_2947_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v_stx_2962_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2966_, lean_object* v_s_2967_){
_start:
{
lean_object* v_cache_2968_; lean_object* v_tokenCache_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2982_; 
v_cache_2968_ = lean_ctor_get(v_s_2967_, 3);
lean_inc_ref(v_cache_2968_);
v_tokenCache_2969_ = lean_ctor_get(v_cache_2968_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_cache_2968_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_cache_2968_, 1);
lean_dec(v_unused_2983_);
v___x_2971_ = v_cache_2968_;
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_tokenCache_2969_);
lean_dec(v_cache_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v_pos_2973_; lean_object* v_startPos_2974_; lean_object* v_token_2975_; uint8_t v___x_2976_; 
v_pos_2973_ = lean_ctor_get(v_s_2967_, 2);
v_startPos_2974_ = lean_ctor_get(v_tokenCache_2969_, 0);
lean_inc(v_startPos_2974_);
v_token_2975_ = lean_ctor_get(v_tokenCache_2969_, 2);
lean_inc(v_token_2975_);
lean_dec_ref(v_tokenCache_2969_);
v___x_2976_ = lean_nat_dec_eq(v_startPos_2974_, v_pos_2973_);
lean_dec(v_startPos_2974_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_dec(v_token_2975_);
lean_del_object(v___x_2971_);
v___x_2977_ = l_Lean_Parser_peekTokenAux(v_c_2966_, v_s_2967_);
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_dec_ref(v_c_2966_);
v___x_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_token_2975_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 1, v___x_2978_);
lean_ctor_set(v___x_2971_, 0, v_s_2967_);
v___x_2980_ = v___x_2971_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_s_2967_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2984_, lean_object* v_c_2985_, lean_object* v_s_2986_){
_start:
{
lean_object* v_pos_2987_; lean_object* v_toInputContext_2988_; uint8_t v___x_2989_; 
v_pos_2987_ = lean_ctor_get(v_s_2986_, 2);
v_toInputContext_2988_ = lean_ctor_get(v_c_2985_, 0);
v___x_2989_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2988_, v_pos_2987_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_inc(v_pos_2987_);
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_box(0);
v___x_2992_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2987_, v___x_2990_, v_includeWhitespace_2984_, v___x_2991_, v_c_2985_, v_s_2986_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec_ref(v_c_2985_);
v___x_2993_ = lean_box(0);
v___x_2994_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2986_, v___x_2993_);
return v___x_2994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2995_, lean_object* v_c_2996_, lean_object* v_s_2997_){
_start:
{
uint8_t v_includeWhitespace_boxed_2998_; lean_object* v_res_2999_; 
v_includeWhitespace_boxed_2998_ = lean_unbox(v_includeWhitespace_2995_);
v_res_2999_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2998_, v_c_2996_, v_s_2997_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_3000_, lean_object* v_expected_3001_, lean_object* v_c_3002_, lean_object* v_s_3003_){
_start:
{
lean_object* v_pos_3004_; lean_object* v_s_3005_; lean_object* v_stxStack_3006_; lean_object* v_errorMsg_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_pos_3004_ = lean_ctor_get(v_s_3003_, 2);
lean_inc(v_pos_3004_);
lean_inc(v_expected_3001_);
v_s_3005_ = l_Lean_Parser_tokenFn(v_expected_3001_, v_c_3002_, v_s_3003_);
v_stxStack_3006_ = lean_ctor_get(v_s_3005_, 0);
lean_inc_ref(v_stxStack_3006_);
v_errorMsg_3007_ = lean_ctor_get(v_s_3005_, 4);
lean_inc(v_errorMsg_3007_);
v___x_3008_ = lean_box(0);
v___x_3009_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3007_, v___x_3008_);
lean_dec(v_errorMsg_3007_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v_stxStack_3006_);
lean_dec(v_pos_3004_);
lean_dec(v_expected_3001_);
lean_dec_ref(v_p_3000_);
return v_s_3005_;
}
else
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3006_);
lean_dec_ref(v_stxStack_3006_);
if (lean_obj_tag(v___x_3010_) == 2)
{
lean_object* v_val_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_val_3011_ = lean_ctor_get(v___x_3010_, 1);
lean_inc_ref(v_val_3011_);
lean_dec_ref_known(v___x_3010_, 2);
v___x_3012_ = lean_apply_1(v_p_3000_, v_val_3011_);
v___x_3013_ = lean_unbox(v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3005_, v_expected_3001_, v_pos_3004_);
return v___x_3014_;
}
else
{
lean_dec(v_pos_3004_);
lean_dec(v_expected_3001_);
return v_s_3005_;
}
}
else
{
lean_object* v___x_3015_; 
lean_dec(v___x_3010_);
lean_dec_ref(v_p_3000_);
v___x_3015_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3005_, v_expected_3001_, v_pos_3004_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_3016_, lean_object* v_s_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_string_dec_eq(v_s_3017_, v_sym_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_3019_, lean_object* v_s_3020_){
_start:
{
uint8_t v_res_3021_; lean_object* v_r_3022_; 
v_res_3021_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_3019_, v_s_3020_);
lean_dec_ref(v_s_3020_);
lean_dec_ref(v_sym_3019_);
v_r_3022_ = lean_box(v_res_3021_);
return v_r_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_3023_, lean_object* v_errorMsg_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___f_3027_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3027_, 0, v_sym_3023_);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3029_, 0, v_errorMsg_3024_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_Lean_Parser_satisfySymbolFn(v___f_3027_, v___x_3029_, v_a_3025_, v_a_3026_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_3031_, lean_object* v_tks_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_sym_3031_);
lean_ctor_set(v___x_3033_, 1, v_tks_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_3034_){
_start:
{
lean_object* v___f_3035_; lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_inc_ref(v_sym_3034_);
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3035_, 0, v_sym_3034_);
v___f_3036_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3038_, 0, v_sym_3034_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3040_, 0, v___f_3035_);
lean_ctor_set(v___x_3040_, 1, v___f_3036_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3045_ = lean_string_append(v___x_3044_, v_sym_3041_);
v___x_3046_ = lean_string_append(v___x_3045_, v___x_3044_);
v___x_3047_ = l_Lean_Parser_symbolFnAux(v_sym_3041_, v___x_3046_, v_a_3042_, v_a_3043_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3048_){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_str_3053_; lean_object* v_startInclusive_3054_; lean_object* v_endExclusive_3055_; lean_object* v_sym_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_string_utf8_byte_size(v_sym_3048_);
v___x_3051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3051_, 0, v_sym_3048_);
lean_ctor_set(v___x_3051_, 1, v___x_3049_);
lean_ctor_set(v___x_3051_, 2, v___x_3050_);
v___x_3052_ = l_String_Slice_trimAscii(v___x_3051_);
v_str_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc_ref(v_str_3053_);
v_startInclusive_3054_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_startInclusive_3054_);
v_endExclusive_3055_ = lean_ctor_get(v___x_3052_, 2);
lean_inc(v_endExclusive_3055_);
lean_dec_ref(v___x_3052_);
v_sym_3056_ = lean_string_utf8_extract(v_str_3053_, v_startInclusive_3054_, v_endExclusive_3055_);
lean_dec(v_endExclusive_3055_);
lean_dec(v_startInclusive_3054_);
lean_dec_ref(v_str_3053_);
lean_inc_ref(v_sym_3056_);
v___x_3057_ = l_Lean_Parser_symbolInfo(v_sym_3056_);
v___x_3058_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3058_, 0, v_sym_3056_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3060_, lean_object* v_errorMsg_3061_, lean_object* v_c_3062_, lean_object* v_s_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v_s_3066_; lean_object* v_stxStack_3070_; lean_object* v_errorMsg_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3064_ = lean_box(0);
lean_inc_ref(v_errorMsg_3061_);
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_errorMsg_3061_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v_s_3066_ = l_Lean_Parser_tokenFn(v___x_3065_, v_c_3062_, v_s_3063_);
v_stxStack_3070_ = lean_ctor_get(v_s_3066_, 0);
lean_inc_ref(v_stxStack_3070_);
v_errorMsg_3071_ = lean_ctor_get(v_s_3066_, 4);
lean_inc(v_errorMsg_3071_);
v___x_3072_ = lean_box(0);
v___x_3073_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3071_, v___x_3072_);
lean_dec(v_errorMsg_3071_);
if (v___x_3073_ == 0)
{
lean_dec_ref(v_stxStack_3070_);
lean_dec_ref(v_errorMsg_3061_);
lean_dec_ref(v_sym_3060_);
return v_s_3066_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3070_);
lean_dec_ref(v_stxStack_3070_);
switch(lean_obj_tag(v___x_3074_))
{
case 2:
{
lean_object* v_val_3075_; uint8_t v___x_3076_; 
v_val_3075_ = lean_ctor_get(v___x_3074_, 1);
lean_inc_ref(v_val_3075_);
lean_dec_ref_known(v___x_3074_, 2);
v___x_3076_ = lean_string_dec_eq(v_sym_3060_, v_val_3075_);
lean_dec_ref(v_val_3075_);
lean_dec_ref(v_sym_3060_);
if (v___x_3076_ == 0)
{
goto v___jp_3067_;
}
else
{
lean_dec_ref(v_errorMsg_3061_);
return v_s_3066_;
}
}
case 3:
{
lean_object* v_rawVal_3077_; lean_object* v_info_3078_; lean_object* v_str_3079_; lean_object* v_startPos_3080_; lean_object* v_stopPos_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_rawVal_3077_ = lean_ctor_get(v___x_3074_, 1);
lean_inc_ref(v_rawVal_3077_);
v_info_3078_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_info_3078_);
lean_dec_ref_known(v___x_3074_, 4);
v_str_3079_ = lean_ctor_get(v_rawVal_3077_, 0);
lean_inc_ref(v_str_3079_);
v_startPos_3080_ = lean_ctor_get(v_rawVal_3077_, 1);
lean_inc(v_startPos_3080_);
v_stopPos_3081_ = lean_ctor_get(v_rawVal_3077_, 2);
lean_inc(v_stopPos_3081_);
lean_dec_ref(v_rawVal_3077_);
v___x_3082_ = lean_string_utf8_extract(v_str_3079_, v_startPos_3080_, v_stopPos_3081_);
lean_dec(v_stopPos_3081_);
lean_dec(v_startPos_3080_);
lean_dec_ref(v_str_3079_);
v___x_3083_ = lean_string_dec_eq(v_sym_3060_, v___x_3082_);
lean_dec_ref(v___x_3082_);
if (v___x_3083_ == 0)
{
lean_dec(v_info_3078_);
lean_dec_ref(v_sym_3060_);
goto v___jp_3067_;
}
else
{
lean_object* v_s_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_dec_ref(v_errorMsg_3061_);
v_s_3084_ = l_Lean_Parser_ParserState_popSyntax(v_s_3066_);
v___x_3085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_info_3078_);
lean_ctor_set(v___x_3085_, 1, v_sym_3060_);
v___x_3086_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3084_, v___x_3085_);
return v___x_3086_;
}
}
default: 
{
lean_dec(v___x_3074_);
lean_dec_ref(v_sym_3060_);
goto v___jp_3067_;
}
}
}
v___jp_3067_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3066_, v_errorMsg_3061_, v___x_3068_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3090_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3091_ = lean_string_append(v___x_3090_, v_sym_3087_);
v___x_3092_ = lean_string_append(v___x_3091_, v___x_3090_);
v___x_3093_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3087_, v___x_3092_, v_a_3088_, v_a_3089_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3098_, uint8_t v_includeIdent_3099_){
_start:
{
lean_object* v___f_3100_; lean_object* v___f_3101_; 
v___f_3100_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3101_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3099_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3103_, 0, v_sym_3098_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3105_, 0, v___f_3100_);
lean_ctor_set(v___x_3105_, 1, v___f_3101_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3106_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_sym_3098_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___f_3100_);
lean_ctor_set(v___x_3109_, 1, v___f_3101_);
lean_ctor_set(v___x_3109_, 2, v___x_3108_);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3110_, lean_object* v_includeIdent_3111_){
_start:
{
uint8_t v_includeIdent_boxed_3112_; lean_object* v_res_3113_; 
v_includeIdent_boxed_3112_ = lean_unbox(v_includeIdent_3111_);
v_res_3113_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3110_, v_includeIdent_boxed_3112_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3114_, uint8_t v_includeIdent_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v_str_3120_; lean_object* v_startInclusive_3121_; lean_object* v_endExclusive_3122_; lean_object* v_sym_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_string_utf8_byte_size(v_sym_3114_);
v___x_3118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3118_, 0, v_sym_3114_);
lean_ctor_set(v___x_3118_, 1, v___x_3116_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
v___x_3119_ = l_String_Slice_trimAscii(v___x_3118_);
v_str_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc_ref(v_str_3120_);
v_startInclusive_3121_ = lean_ctor_get(v___x_3119_, 1);
lean_inc(v_startInclusive_3121_);
v_endExclusive_3122_ = lean_ctor_get(v___x_3119_, 2);
lean_inc(v_endExclusive_3122_);
lean_dec_ref(v___x_3119_);
v_sym_3123_ = lean_string_utf8_extract(v_str_3120_, v_startInclusive_3121_, v_endExclusive_3122_);
lean_dec(v_endExclusive_3122_);
lean_dec(v_startInclusive_3121_);
lean_dec_ref(v_str_3120_);
lean_inc_ref(v_sym_3123_);
v___x_3124_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3123_, v_includeIdent_3115_);
v___x_3125_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3125_, 0, v_sym_3123_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3127_, lean_object* v_includeIdent_3128_){
_start:
{
uint8_t v_includeIdent_boxed_3129_; lean_object* v_res_3130_; 
v_includeIdent_boxed_3129_ = lean_unbox(v_includeIdent_3128_);
v_res_3130_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3127_, v_includeIdent_boxed_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3131_, lean_object* v_errorMsg_3132_, lean_object* v_j_3133_, lean_object* v_c_3134_, lean_object* v_s_3135_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_string_utf8_at_end(v_sym_3131_, v_j_3133_);
if (v___x_3136_ == 0)
{
lean_object* v_pos_3137_; lean_object* v_toInputContext_3138_; uint8_t v___x_3139_; 
v_pos_3137_ = lean_ctor_get(v_s_3135_, 2);
v_toInputContext_3138_ = lean_ctor_get(v_c_3134_, 0);
v___x_3139_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3138_, v_pos_3137_);
if (v___x_3139_ == 0)
{
lean_object* v_inputString_3140_; uint32_t v___x_3141_; uint32_t v___x_3142_; uint8_t v___x_3143_; 
v_inputString_3140_ = lean_ctor_get(v_toInputContext_3138_, 0);
v___x_3141_ = lean_string_utf8_get_fast(v_sym_3131_, v_j_3133_);
v___x_3142_ = lean_string_utf8_get_fast(v_inputString_3140_, v_pos_3137_);
v___x_3143_ = lean_uint32_dec_eq(v___x_3141_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; 
lean_dec(v_j_3133_);
v___x_3144_ = l_Lean_Parser_ParserState_mkError(v_s_3135_, v_errorMsg_3132_);
return v___x_3144_;
}
else
{
if (v___x_3139_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_inc(v_pos_3137_);
v___x_3145_ = lean_string_utf8_next_fast(v_sym_3131_, v_j_3133_);
lean_dec(v_j_3133_);
v___x_3146_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3135_, v_c_3134_, v_pos_3137_);
lean_dec(v_pos_3137_);
v_j_3133_ = v___x_3145_;
v_s_3135_ = v___x_3146_;
goto _start;
}
else
{
lean_object* v___x_3148_; 
lean_dec(v_j_3133_);
v___x_3148_ = l_Lean_Parser_ParserState_mkError(v_s_3135_, v_errorMsg_3132_);
return v___x_3148_;
}
}
}
else
{
lean_object* v___x_3149_; 
lean_dec(v_j_3133_);
v___x_3149_ = l_Lean_Parser_ParserState_mkError(v_s_3135_, v_errorMsg_3132_);
return v___x_3149_;
}
}
else
{
lean_dec(v_j_3133_);
lean_dec_ref(v_errorMsg_3132_);
return v_s_3135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3150_, lean_object* v_errorMsg_3151_, lean_object* v_j_3152_, lean_object* v_c_3153_, lean_object* v_s_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3150_, v_errorMsg_3151_, v_j_3152_, v_c_3153_, v_s_3154_);
lean_dec_ref(v_c_3153_);
lean_dec_ref(v_sym_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3156_, lean_object* v_errorMsg_3157_, lean_object* v_j_3158_, lean_object* v_c_3159_, lean_object* v_s_3160_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3156_, v_errorMsg_3157_, v_j_3158_, v_c_3159_, v_s_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3162_, lean_object* v_errorMsg_3163_, lean_object* v_j_3164_, lean_object* v_c_3165_, lean_object* v_s_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_Parser_strAux(v_sym_3162_, v_errorMsg_3163_, v_j_3164_, v_c_3165_, v_s_3166_);
lean_dec_ref(v_c_3165_);
lean_dec_ref(v_sym_3162_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3168_, lean_object* v_i_3169_){
_start:
{
lean_object* v_zero_3170_; uint8_t v_isZero_3171_; 
v_zero_3170_ = lean_unsigned_to_nat(0u);
v_isZero_3171_ = lean_nat_dec_eq(v_i_3169_, v_zero_3170_);
if (v_isZero_3171_ == 1)
{
lean_object* v___x_3172_; 
lean_dec(v_i_3169_);
v___x_3172_ = lean_box(0);
return v___x_3172_;
}
else
{
lean_object* v_one_3173_; lean_object* v_n_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_one_3173_ = lean_unsigned_to_nat(1u);
v_n_3174_ = lean_nat_sub(v_i_3169_, v_one_3173_);
lean_dec(v_i_3169_);
v___x_3175_ = l_Subarray_get___redArg(v_as_3168_, v_n_3174_);
v___x_3176_ = l_Lean_Syntax_isNone(v___x_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; 
lean_dec(v_n_3174_);
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
return v___x_3177_;
}
else
{
lean_dec(v___x_3175_);
v_i_3169_ = v_n_3174_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3179_, lean_object* v_i_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3179_, v_i_3180_);
lean_dec_ref(v_as_3179_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3182_){
_start:
{
lean_object* v___x_3183_; lean_object* v_start_3184_; lean_object* v_stop_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3183_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3182_);
v_start_3184_ = lean_ctor_get(v___x_3183_, 1);
lean_inc(v_start_3184_);
v_stop_3185_ = lean_ctor_get(v___x_3183_, 2);
lean_inc(v_stop_3185_);
v___x_3186_ = lean_nat_sub(v_stop_3185_, v_start_3184_);
lean_dec(v_start_3184_);
lean_dec(v_stop_3185_);
v___x_3187_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3183_, v___x_3186_);
lean_dec_ref(v___x_3183_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_box(0);
return v___x_3188_;
}
else
{
lean_object* v_val_3189_; 
v_val_3189_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_val_3189_);
lean_dec_ref_known(v___x_3187_, 1);
return v_val_3189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3190_, lean_object* v_i_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3190_, v_i_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3194_, lean_object* v_i_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3194_, v_i_3195_, v_a_3196_);
lean_dec_ref(v_as_3194_);
return v_res_3197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_Syntax_getTailInfo(v_prev_3198_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_trailing_3200_; lean_object* v_startPos_3201_; lean_object* v_stopPos_3202_; uint8_t v___x_3203_; 
v_trailing_3200_ = lean_ctor_get(v___x_3199_, 2);
lean_inc_ref(v_trailing_3200_);
lean_dec_ref_known(v___x_3199_, 4);
v_startPos_3201_ = lean_ctor_get(v_trailing_3200_, 1);
lean_inc(v_startPos_3201_);
v_stopPos_3202_ = lean_ctor_get(v_trailing_3200_, 2);
lean_inc(v_stopPos_3202_);
lean_dec_ref(v_trailing_3200_);
v___x_3203_ = lean_nat_dec_lt(v_startPos_3201_, v_stopPos_3202_);
lean_dec(v_stopPos_3202_);
lean_dec(v_startPos_3201_);
return v___x_3203_;
}
else
{
uint8_t v___x_3204_; 
lean_dec(v___x_3199_);
v___x_3204_ = 0;
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3205_){
_start:
{
uint8_t v_res_3206_; lean_object* v_r_3207_; 
v_res_3206_ = l_Lean_Parser_checkTailWs(v_prev_3205_);
lean_dec(v_prev_3205_);
v_r_3207_ = lean_box(v_res_3206_);
return v_r_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3208_, lean_object* v_s_3209_){
_start:
{
lean_object* v_stxStack_3210_; lean_object* v_prev_3211_; uint8_t v___x_3212_; 
v_stxStack_3210_ = lean_ctor_get(v_s_3209_, 0);
lean_inc_ref(v_stxStack_3210_);
v_prev_3211_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3210_);
v___x_3212_ = l_Lean_Parser_checkTailWs(v_prev_3211_);
lean_dec(v_prev_3211_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Parser_ParserState_mkError(v_s_3209_, v_errorMsg_3208_);
return v___x_3213_;
}
else
{
lean_dec_ref(v_errorMsg_3208_);
return v_s_3209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3214_, lean_object* v_x_3215_, lean_object* v_s_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3214_, v_s_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3218_, lean_object* v_x_3219_, lean_object* v_s_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3218_, v_x_3219_, v_s_3220_);
lean_dec_ref(v_x_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3222_){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3224_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3224_, 0, v_errorMsg_3222_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3234_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3235_ = l_Lean_addBuiltinDocString(v___x_3233_, v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3238_){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = l_String_instInhabitedSlice;
v___x_3240_ = lean_panic_fn_borrowed(v___x_3239_, v_msg_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3241_, lean_object* v_a_3242_, uint8_t v_b_3243_){
_start:
{
lean_object* v_str_3244_; lean_object* v_startInclusive_3245_; lean_object* v_endExclusive_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v_str_3244_ = lean_ctor_get(v_s_3241_, 0);
v_startInclusive_3245_ = lean_ctor_get(v_s_3241_, 1);
v_endExclusive_3246_ = lean_ctor_get(v_s_3241_, 2);
v___x_3247_ = lean_nat_sub(v_endExclusive_3246_, v_startInclusive_3245_);
v___x_3248_ = lean_nat_dec_eq(v_a_3242_, v___x_3247_);
lean_dec(v___x_3247_);
if (v___x_3248_ == 0)
{
uint32_t v___x_3249_; lean_object* v___x_3250_; uint32_t v___x_3251_; uint8_t v___x_3252_; 
v___x_3249_ = 10;
v___x_3250_ = lean_nat_add(v_startInclusive_3245_, v_a_3242_);
lean_dec(v_a_3242_);
v___x_3251_ = lean_string_utf8_get_fast(v_str_3244_, v___x_3250_);
v___x_3252_ = lean_uint32_dec_eq(v___x_3251_, v___x_3249_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = lean_string_utf8_next_fast(v_str_3244_, v___x_3250_);
lean_dec(v___x_3250_);
v___x_3254_ = lean_nat_sub(v___x_3253_, v_startInclusive_3245_);
v_a_3242_ = v___x_3254_;
v_b_3243_ = v___x_3252_;
goto _start;
}
else
{
lean_dec(v___x_3250_);
return v___x_3252_;
}
}
else
{
lean_dec(v_a_3242_);
return v_b_3243_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3256_, lean_object* v_a_3257_, lean_object* v_b_3258_){
_start:
{
uint8_t v_b_boxed_3259_; uint8_t v_res_3260_; lean_object* v_r_3261_; 
v_b_boxed_3259_ = lean_unbox(v_b_3258_);
v_res_3260_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3256_, v_a_3257_, v_b_boxed_3259_);
lean_dec_ref(v_s_3256_);
v_r_3261_ = lean_box(v_res_3260_);
return v_r_3261_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3262_){
_start:
{
lean_object* v_searcher_3263_; uint8_t v___x_3264_; uint8_t v___x_3265_; 
v_searcher_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = 0;
v___x_3265_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3262_, v_searcher_3263_, v___x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3266_){
_start:
{
uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_res_3267_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3266_);
lean_dec_ref(v_s_3266_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3272_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3273_ = lean_unsigned_to_nat(14u);
v___x_3274_ = lean_unsigned_to_nat(22u);
v___x_3275_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3276_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3277_ = l_mkPanicMessageWithDecl(v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_, v___x_3272_);
return v___x_3277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3278_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Syntax_getTailInfo(v_prev_3278_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_trailing_3284_; lean_object* v_str_3285_; lean_object* v_startPos_3286_; lean_object* v_stopPos_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3298_; 
v_trailing_3284_ = lean_ctor_get(v___x_3283_, 2);
lean_inc_ref(v_trailing_3284_);
lean_dec_ref_known(v___x_3283_, 4);
v_str_3285_ = lean_ctor_get(v_trailing_3284_, 0);
v_startPos_3286_ = lean_ctor_get(v_trailing_3284_, 1);
v_stopPos_3287_ = lean_ctor_get(v_trailing_3284_, 2);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_trailing_3284_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3289_ = v_trailing_3284_;
v_isShared_3290_ = v_isSharedCheck_3298_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_stopPos_3287_);
lean_inc(v_startPos_3286_);
lean_inc(v_str_3285_);
lean_dec(v_trailing_3284_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3298_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
uint8_t v___x_3291_; 
v___x_3291_ = lean_string_is_valid_pos(v_str_3285_, v_startPos_3286_);
if (v___x_3291_ == 0)
{
lean_del_object(v___x_3289_);
lean_dec(v_stopPos_3287_);
lean_dec(v_startPos_3286_);
lean_dec_ref(v_str_3285_);
goto v___jp_3279_;
}
else
{
uint8_t v___x_3292_; 
v___x_3292_ = lean_string_is_valid_pos(v_str_3285_, v_stopPos_3287_);
if (v___x_3292_ == 0)
{
lean_del_object(v___x_3289_);
lean_dec(v_stopPos_3287_);
lean_dec(v_startPos_3286_);
lean_dec_ref(v_str_3285_);
goto v___jp_3279_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_nat_dec_le(v_startPos_3286_, v_stopPos_3287_);
if (v___x_3293_ == 0)
{
lean_del_object(v___x_3289_);
lean_dec(v_stopPos_3287_);
lean_dec(v_startPos_3286_);
lean_dec_ref(v_str_3285_);
goto v___jp_3279_;
}
else
{
lean_object* v___x_3295_; 
if (v_isShared_3290_ == 0)
{
v___x_3295_ = v___x_3289_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_str_3285_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_startPos_3286_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_stopPos_3287_);
v___x_3295_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
uint8_t v___x_3296_; 
v___x_3296_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3295_);
lean_dec_ref(v___x_3295_);
return v___x_3296_;
}
}
}
}
}
}
else
{
uint8_t v___x_3299_; 
lean_dec(v___x_3283_);
v___x_3299_ = 0;
return v___x_3299_;
}
v___jp_3279_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3280_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3281_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3280_);
v___x_3282_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3281_);
lean_dec_ref(v___x_3281_);
return v___x_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Lean_Parser_checkTailLinebreak(v_prev_3300_);
lean_dec(v_prev_3300_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3303_, lean_object* v_inst_3304_, lean_object* v_R_3305_, lean_object* v_a_3306_, uint8_t v_b_3307_, lean_object* v_c_3308_){
_start:
{
uint8_t v___x_3309_; 
v___x_3309_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3303_, v_a_3306_, v_b_3307_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3310_, lean_object* v_inst_3311_, lean_object* v_R_3312_, lean_object* v_a_3313_, lean_object* v_b_3314_, lean_object* v_c_3315_){
_start:
{
uint8_t v_b_boxed_3316_; uint8_t v_res_3317_; lean_object* v_r_3318_; 
v_b_boxed_3316_ = lean_unbox(v_b_3314_);
v_res_3317_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3310_, v_inst_3311_, v_R_3312_, v_a_3313_, v_b_boxed_3316_, v_c_3315_);
lean_dec_ref(v_s_3310_);
v_r_3318_ = lean_box(v_res_3317_);
return v_r_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3319_, lean_object* v_s_3320_){
_start:
{
lean_object* v_stxStack_3321_; lean_object* v_prev_3322_; uint8_t v___x_3323_; 
v_stxStack_3321_ = lean_ctor_get(v_s_3320_, 0);
v_prev_3322_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3321_);
v___x_3323_ = l_Lean_Parser_checkTailLinebreak(v_prev_3322_);
lean_dec(v_prev_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Parser_ParserState_mkError(v_s_3320_, v_errorMsg_3319_);
return v___x_3324_;
}
else
{
lean_dec_ref(v_errorMsg_3319_);
return v_s_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3325_, lean_object* v_x_3326_, lean_object* v_s_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3325_, v_s_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3329_, lean_object* v_x_3330_, lean_object* v_s_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3329_, v_x_3330_, v_s_3331_);
lean_dec_ref(v_x_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3333_){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3335_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3335_, 0, v_errorMsg_3333_);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3345_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3346_ = l_Lean_addBuiltinDocString(v___x_3344_, v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Syntax_getTailInfo(v_prev_3349_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_trailing_3351_; lean_object* v_startPos_3352_; lean_object* v_stopPos_3353_; uint8_t v___x_3354_; 
v_trailing_3351_ = lean_ctor_get(v___x_3350_, 2);
lean_inc_ref(v_trailing_3351_);
lean_dec_ref_known(v___x_3350_, 4);
v_startPos_3352_ = lean_ctor_get(v_trailing_3351_, 1);
lean_inc(v_startPos_3352_);
v_stopPos_3353_ = lean_ctor_get(v_trailing_3351_, 2);
lean_inc(v_stopPos_3353_);
lean_dec_ref(v_trailing_3351_);
v___x_3354_ = lean_nat_dec_eq(v_stopPos_3353_, v_startPos_3352_);
lean_dec(v_startPos_3352_);
lean_dec(v_stopPos_3353_);
return v___x_3354_;
}
else
{
uint8_t v___x_3355_; 
lean_dec(v___x_3350_);
v___x_3355_ = 0;
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3356_){
_start:
{
uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_res_3357_ = l_Lean_Parser_checkTailNoWs(v_prev_3356_);
lean_dec(v_prev_3356_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3359_, lean_object* v_s_3360_){
_start:
{
lean_object* v_stxStack_3361_; lean_object* v_prev_3362_; uint8_t v___x_3363_; 
v_stxStack_3361_ = lean_ctor_get(v_s_3360_, 0);
lean_inc_ref(v_stxStack_3361_);
v_prev_3362_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3361_);
v___x_3363_ = l_Lean_Parser_checkTailNoWs(v_prev_3362_);
lean_dec(v_prev_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lean_Parser_ParserState_mkError(v_s_3360_, v_errorMsg_3359_);
return v___x_3364_;
}
else
{
lean_dec_ref(v_errorMsg_3359_);
return v_s_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3365_, lean_object* v_x_3366_, lean_object* v_s_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3365_, v_s_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3369_, lean_object* v_x_3370_, lean_object* v_s_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3369_, v_x_3370_, v_s_3371_);
lean_dec_ref(v_x_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3373_){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3375_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3375_, 0, v_errorMsg_3373_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3385_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3386_ = l_Lean_addBuiltinDocString(v___x_3384_, v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3388_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3389_, lean_object* v_asciiSym_3390_, lean_object* v_s_3391_){
_start:
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_string_dec_eq(v_s_3391_, v_sym_3389_);
if (v___x_3392_ == 0)
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_string_dec_eq(v_s_3391_, v_asciiSym_3390_);
return v___x_3393_;
}
else
{
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3394_, lean_object* v_asciiSym_3395_, lean_object* v_s_3396_){
_start:
{
uint8_t v_res_3397_; lean_object* v_r_3398_; 
v_res_3397_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3394_, v_asciiSym_3395_, v_s_3396_);
lean_dec_ref(v_s_3396_);
lean_dec_ref(v_asciiSym_3395_);
lean_dec_ref(v_sym_3394_);
v_r_3398_ = lean_box(v_res_3397_);
return v_r_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3399_, lean_object* v_asciiSym_3400_, lean_object* v_expected_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___f_3404_; lean_object* v___x_3405_; 
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3404_, 0, v_sym_3399_);
lean_closure_set(v___f_3404_, 1, v_asciiSym_3400_);
v___x_3405_ = l_Lean_Parser_satisfySymbolFn(v___f_3404_, v_expected_3401_, v_a_3402_, v_a_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3406_, lean_object* v_sym_3407_, lean_object* v_tks_3408_){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v_asciiSym_3406_);
lean_ctor_set(v___x_3409_, 1, v_tks_3408_);
v___x_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3410_, 0, v_sym_3407_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3411_, lean_object* v_asciiSym_3412_){
_start:
{
lean_object* v___f_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_inc_ref(v_sym_3411_);
lean_inc_ref(v_asciiSym_3412_);
v___f_3413_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3413_, 0, v_asciiSym_3412_);
lean_closure_set(v___f_3413_, 1, v_sym_3411_);
v___f_3414_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3415_ = lean_box(0);
v___x_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3416_, 0, v_asciiSym_3412_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3417_, 0, v_sym_3411_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
v___x_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___f_3413_);
lean_ctor_set(v___x_3419_, 1, v___f_3414_);
lean_ctor_set(v___x_3419_, 2, v___x_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3421_, lean_object* v_asciiSym_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3425_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3426_ = lean_string_append(v___x_3425_, v_sym_3421_);
v___x_3427_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3428_ = lean_string_append(v___x_3426_, v___x_3427_);
v___x_3429_ = lean_string_append(v___x_3428_, v_asciiSym_3422_);
v___x_3430_ = lean_string_append(v___x_3429_, v___x_3425_);
v___x_3431_ = lean_box(0);
v___x_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3421_, v_asciiSym_3422_, v___x_3432_, v_a_3423_, v_a_3424_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3434_, lean_object* v_asciiSym_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v_str_3440_; lean_object* v_startInclusive_3441_; lean_object* v_endExclusive_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3459_; 
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = lean_string_utf8_byte_size(v_sym_3434_);
v___x_3438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3438_, 0, v_sym_3434_);
lean_ctor_set(v___x_3438_, 1, v___x_3436_);
lean_ctor_set(v___x_3438_, 2, v___x_3437_);
v___x_3439_ = l_String_Slice_trimAscii(v___x_3438_);
v_str_3440_ = lean_ctor_get(v___x_3439_, 0);
v_startInclusive_3441_ = lean_ctor_get(v___x_3439_, 1);
v_endExclusive_3442_ = lean_ctor_get(v___x_3439_, 2);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3444_ = v___x_3439_;
v_isShared_3445_ = v_isSharedCheck_3459_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_endExclusive_3442_);
lean_inc(v_startInclusive_3441_);
lean_inc(v_str_3440_);
lean_dec(v___x_3439_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3459_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3446_ = lean_string_utf8_byte_size(v_asciiSym_3435_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 2, v___x_3446_);
lean_ctor_set(v___x_3444_, 1, v___x_3436_);
lean_ctor_set(v___x_3444_, 0, v_asciiSym_3435_);
v___x_3448_ = v___x_3444_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_asciiSym_3435_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; lean_object* v_str_3450_; lean_object* v_startInclusive_3451_; lean_object* v_endExclusive_3452_; lean_object* v_sym_3453_; lean_object* v_asciiSym_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3449_ = l_String_Slice_trimAscii(v___x_3448_);
v_str_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc_ref(v_str_3450_);
v_startInclusive_3451_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_startInclusive_3451_);
v_endExclusive_3452_ = lean_ctor_get(v___x_3449_, 2);
lean_inc(v_endExclusive_3452_);
lean_dec_ref(v___x_3449_);
v_sym_3453_ = lean_string_utf8_extract(v_str_3440_, v_startInclusive_3441_, v_endExclusive_3442_);
lean_dec(v_endExclusive_3442_);
lean_dec(v_startInclusive_3441_);
lean_dec_ref(v_str_3440_);
v_asciiSym_3454_ = lean_string_utf8_extract(v_str_3450_, v_startInclusive_3451_, v_endExclusive_3452_);
lean_dec(v_endExclusive_3452_);
lean_dec(v_startInclusive_3451_);
lean_dec_ref(v_str_3450_);
lean_inc_ref(v_asciiSym_3454_);
lean_inc_ref(v_sym_3453_);
v___x_3455_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3453_, v_asciiSym_3454_);
v___x_3456_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3456_, 0, v_sym_3453_);
lean_closure_set(v___x_3456_, 1, v_asciiSym_3454_);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3460_, lean_object* v_asciiSym_3461_, uint8_t v_preserveForPP_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3460_, v_asciiSym_3461_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3464_, lean_object* v_asciiSym_3465_, lean_object* v_preserveForPP_3466_){
_start:
{
uint8_t v_preserveForPP_boxed_3467_; lean_object* v_res_3468_; 
v_preserveForPP_boxed_3467_ = lean_unbox(v_preserveForPP_3466_);
v_res_3468_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3464_, v_asciiSym_3465_, v_preserveForPP_boxed_3467_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3469_){
_start:
{
lean_object* v___f_3470_; lean_object* v___f_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___f_3470_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3471_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3473_, 0, v_k_3469_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3475_, 0, v___f_3470_);
lean_ctor_set(v___x_3475_, 1, v___f_3471_);
lean_ctor_set(v___x_3475_, 2, v___x_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3476_, lean_object* v_desc_3477_, lean_object* v_c_3478_, lean_object* v_s_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v_s_3482_; lean_object* v_stxStack_3483_; lean_object* v_errorMsg_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3480_ = lean_box(0);
lean_inc_ref(v_desc_3477_);
v___x_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3481_, 0, v_desc_3477_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v_s_3482_ = l_Lean_Parser_tokenFn(v___x_3481_, v_c_3478_, v_s_3479_);
v_stxStack_3483_ = lean_ctor_get(v_s_3482_, 0);
lean_inc_ref(v_stxStack_3483_);
v_errorMsg_3484_ = lean_ctor_get(v_s_3482_, 4);
lean_inc(v_errorMsg_3484_);
v___x_3485_ = lean_box(0);
v___x_3486_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3484_, v___x_3485_);
lean_dec(v_errorMsg_3484_);
if (v___x_3486_ == 0)
{
lean_dec_ref(v_stxStack_3483_);
lean_dec_ref(v_desc_3477_);
return v_s_3482_;
}
else
{
lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3487_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3483_);
lean_dec_ref(v_stxStack_3483_);
v___x_3488_ = l_Lean_Syntax_isOfKind(v___x_3487_, v_k_3476_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3482_, v_desc_3477_, v___x_3489_);
return v___x_3490_;
}
else
{
lean_dec_ref(v_desc_3477_);
return v_s_3482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3491_, lean_object* v_desc_3492_, lean_object* v_c_3493_, lean_object* v_s_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Parser_expectTokenFn(v_k_3491_, v_desc_3492_, v_c_3493_, v_s_3494_);
lean_dec(v_k_3491_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3499_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3500_ = l_Lean_Parser_expectTokenFn(v___x_3498_, v___x_3499_, v_a_3496_, v_a_3497_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3502_ = l_Lean_Parser_mkAtomicInfo(v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3504_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3503_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3510_, lean_object* v_s_3511_){
_start:
{
lean_object* v_pos_3512_; uint8_t v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_pos_3512_ = lean_ctor_get(v_s_3511_, 2);
lean_inc(v_pos_3512_);
v___x_3513_ = 1;
v___x_3514_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3515_ = l_Lean_Parser_hexNumberFn(v_pos_3512_, v___x_3513_, v___x_3514_, v_ctx_3510_, v_s_3511_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3517_ = l_Lean_Parser_mkAtomicInfo(v___x_3516_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3519_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___x_3518_);
return v___x_3520_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3526_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3527_ = l_Lean_Parser_expectTokenFn(v___x_3525_, v___x_3526_, v_a_3523_, v_a_3524_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3529_ = l_Lean_Parser_mkAtomicInfo(v___x_3528_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3531_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
lean_ctor_set(v___x_3532_, 1, v___x_3530_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3538_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3539_ = l_Lean_Parser_expectTokenFn(v___x_3537_, v___x_3538_, v_a_3535_, v_a_3536_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3541_ = l_Lean_Parser_mkAtomicInfo(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3543_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v___x_3542_);
return v___x_3544_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3550_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3551_ = l_Lean_Parser_expectTokenFn(v___x_3549_, v___x_3550_, v_a_3547_, v_a_3548_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3553_ = l_Lean_Parser_mkAtomicInfo(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3555_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
lean_ctor_set(v___x_3556_, 1, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3565_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3566_ = l_Lean_Parser_expectTokenFn(v___x_3564_, v___x_3565_, v_a_3562_, v_a_3563_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3568_ = l_Lean_Parser_mkAtomicInfo(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3570_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v___x_3569_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3579_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3580_ = l_Lean_Parser_expectTokenFn(v___x_3578_, v___x_3579_, v_a_3576_, v_a_3577_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3582_ = l_Lean_Parser_mkAtomicInfo(v___x_3581_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3584_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v___x_3583_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3598_, lean_object* v_c_3599_, lean_object* v_s_3600_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_s_3603_; lean_object* v_stxStack_3604_; lean_object* v_errorMsg_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3601_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3602_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3603_ = l_Lean_Parser_tokenFn(v___x_3602_, v_c_3599_, v_s_3600_);
v_stxStack_3604_ = lean_ctor_get(v_s_3603_, 0);
lean_inc_ref(v_stxStack_3604_);
v_errorMsg_3605_ = lean_ctor_get(v_s_3603_, 4);
lean_inc(v_errorMsg_3605_);
v___x_3606_ = lean_box(0);
v___x_3607_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3605_, v___x_3606_);
lean_dec(v_errorMsg_3605_);
if (v___x_3607_ == 0)
{
lean_dec_ref(v_stxStack_3604_);
lean_dec(v_id_3598_);
return v_s_3603_;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3604_);
lean_dec_ref(v_stxStack_3604_);
if (lean_obj_tag(v___x_3608_) == 3)
{
lean_object* v_val_3609_; uint8_t v___x_3610_; 
v_val_3609_ = lean_ctor_get(v___x_3608_, 2);
lean_inc(v_val_3609_);
lean_dec_ref_known(v___x_3608_, 4);
v___x_3610_ = lean_name_eq(v_val_3609_, v_id_3598_);
lean_dec(v_val_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3611_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3598_, v___x_3607_);
v___x_3613_ = lean_string_append(v___x_3611_, v___x_3612_);
lean_dec_ref(v___x_3612_);
v___x_3614_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3615_ = lean_string_append(v___x_3613_, v___x_3614_);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3603_, v___x_3615_, v___x_3616_);
return v___x_3617_;
}
else
{
lean_dec(v_id_3598_);
return v_s_3603_;
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_dec(v___x_3608_);
lean_dec(v_id_3598_);
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3603_, v___x_3601_, v___x_3618_);
return v___x_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3620_){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3622_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3622_, 0, v_id_3620_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3627_, lean_object* v_s_3628_){
_start:
{
lean_object* v_pos_3630_; lean_object* v_str_3631_; lean_object* v_trailing_3632_; lean_object* v_s_3633_; lean_object* v_stxStack_3645_; lean_object* v_pos_3646_; uint8_t v___x_3649_; 
v_stxStack_3645_ = lean_ctor_get(v_s_3628_, 0);
v_pos_3646_ = lean_ctor_get(v_s_3628_, 2);
v___x_3649_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3645_);
if (v___x_3649_ == 0)
{
lean_object* v_prev_3650_; lean_object* v___x_3651_; 
v_prev_3650_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3645_);
v___x_3651_ = l_Lean_Syntax_getTailInfo(v_prev_3650_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_leading_3652_; lean_object* v_pos_3653_; lean_object* v_trailing_3654_; lean_object* v_endPos_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3666_; 
v_leading_3652_ = lean_ctor_get(v___x_3651_, 0);
v_pos_3653_ = lean_ctor_get(v___x_3651_, 1);
v_trailing_3654_ = lean_ctor_get(v___x_3651_, 2);
v_endPos_3655_ = lean_ctor_get(v___x_3651_, 3);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3657_ = v___x_3651_;
v_isShared_3658_ = v_isSharedCheck_3666_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_endPos_3655_);
lean_inc(v_trailing_3654_);
lean_inc(v_pos_3653_);
lean_inc(v_leading_3652_);
lean_dec(v___x_3651_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3666_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_str_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_inc_n(v_endPos_3655_, 2);
v_str_3659_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3627_, v_endPos_3655_);
v___x_3660_ = l_Lean_Parser_ParserState_popSyntax(v_s_3628_);
lean_inc_ref(v_str_3659_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 2, v_str_3659_);
v___x_3662_ = v___x_3657_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_leading_3652_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_pos_3653_);
lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_str_3659_);
lean_ctor_set(v_reuseFailAlloc_3665_, 3, v_endPos_3655_);
v___x_3662_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v_s_3664_; 
v___x_3663_ = l_Lean_Syntax_setTailInfo(v_prev_3650_, v___x_3662_);
v_s_3664_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3660_, v___x_3663_);
v_pos_3630_ = v_endPos_3655_;
v_str_3631_ = v_str_3659_;
v_trailing_3632_ = v_trailing_3654_;
v_s_3633_ = v_s_3664_;
goto v___jp_3629_;
}
}
}
else
{
lean_inc(v_pos_3646_);
lean_dec(v___x_3651_);
lean_dec(v_prev_3650_);
goto v___jp_3647_;
}
}
else
{
lean_inc(v_pos_3646_);
goto v___jp_3647_;
}
v___jp_3629_:
{
lean_object* v_info_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_ident_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_inc(v_pos_3630_);
lean_inc_ref(v_str_3631_);
v_info_3634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3634_, 0, v_str_3631_);
lean_ctor_set(v_info_3634_, 1, v_pos_3630_);
lean_ctor_set(v_info_3634_, 2, v_trailing_3632_);
lean_ctor_set(v_info_3634_, 3, v_pos_3630_);
v___x_3635_ = lean_box(0);
v___x_3636_ = lean_box(0);
v_ident_3637_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3637_, 0, v_info_3634_);
lean_ctor_set(v_ident_3637_, 1, v_str_3631_);
lean_ctor_set(v_ident_3637_, 2, v___x_3635_);
lean_ctor_set(v_ident_3637_, 3, v___x_3636_);
v___x_3638_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3639_ = lean_unsigned_to_nat(1u);
v___x_3640_ = lean_mk_empty_array_with_capacity(v___x_3639_);
v___x_3641_ = lean_array_push(v___x_3640_, v_ident_3637_);
v___x_3642_ = lean_box(2);
v___x_3643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___x_3638_);
lean_ctor_set(v___x_3643_, 2, v___x_3641_);
v___x_3644_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3633_, v___x_3643_);
return v___x_3644_;
}
v___jp_3647_:
{
lean_object* v_str_3648_; 
lean_inc(v_pos_3646_);
v_str_3648_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3627_, v_pos_3646_);
lean_inc_ref(v_str_3648_);
v_pos_3630_ = v_pos_3646_;
v_str_3631_ = v_str_3648_;
v_trailing_3632_ = v_str_3648_;
v_s_3633_ = v_s_3628_;
goto v___jp_3629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3667_, lean_object* v_s_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_Parser_hygieneInfoFn(v_c_3667_, v_s_3668_);
lean_dec_ref(v_c_3667_);
return v_res_3669_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3671_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3672_ = l_Lean_Parser_nodeInfo(v___x_3671_, v___x_3670_);
return v___x_3672_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3673_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3674_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
lean_ctor_set(v___x_3675_, 1, v___x_3673_);
return v___x_3675_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3677_, lean_object* v_startStackSize_3678_){
_start:
{
lean_object* v_node_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_node_3679_ = l_Lean_Parser_SyntaxStack_back(v_s_3677_);
v___x_3680_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3677_, v_startStackSize_3678_);
v___x_3681_ = l_Lean_Parser_SyntaxStack_push(v___x_3680_, v_node_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3682_, lean_object* v_startStackSize_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_Parser_ParserState_keepTop(v_s_3682_, v_startStackSize_3683_);
lean_dec(v_startStackSize_3683_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3685_, lean_object* v_oldStackSize_3686_){
_start:
{
lean_object* v_stxStack_3687_; lean_object* v_lhsPrec_3688_; lean_object* v_pos_3689_; lean_object* v_cache_3690_; lean_object* v_errorMsg_3691_; lean_object* v_recoveredErrors_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3700_; 
v_stxStack_3687_ = lean_ctor_get(v_s_3685_, 0);
v_lhsPrec_3688_ = lean_ctor_get(v_s_3685_, 1);
v_pos_3689_ = lean_ctor_get(v_s_3685_, 2);
v_cache_3690_ = lean_ctor_get(v_s_3685_, 3);
v_errorMsg_3691_ = lean_ctor_get(v_s_3685_, 4);
v_recoveredErrors_3692_ = lean_ctor_get(v_s_3685_, 5);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_s_3685_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3694_ = v_s_3685_;
v_isShared_3695_ = v_isSharedCheck_3700_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_recoveredErrors_3692_);
lean_inc(v_errorMsg_3691_);
lean_inc(v_cache_3690_);
lean_inc(v_pos_3689_);
lean_inc(v_lhsPrec_3688_);
lean_inc(v_stxStack_3687_);
lean_dec(v_s_3685_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3700_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3687_, v_oldStackSize_3686_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3696_);
v___x_3698_ = v___x_3694_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_lhsPrec_3688_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v_pos_3689_);
lean_ctor_set(v_reuseFailAlloc_3699_, 3, v_cache_3690_);
lean_ctor_set(v_reuseFailAlloc_3699_, 4, v_errorMsg_3691_);
lean_ctor_set(v_reuseFailAlloc_3699_, 5, v_recoveredErrors_3692_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3701_, lean_object* v_oldStackSize_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Parser_ParserState_keepNewError(v_s_3701_, v_oldStackSize_3702_);
lean_dec(v_oldStackSize_3702_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3704_, lean_object* v_oldStackSize_3705_, lean_object* v_oldStopPos_3706_, lean_object* v_oldError_3707_, lean_object* v_oldLhsPrec_3708_){
_start:
{
lean_object* v_stxStack_3709_; lean_object* v_cache_3710_; lean_object* v_recoveredErrors_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3719_; 
v_stxStack_3709_ = lean_ctor_get(v_s_3704_, 0);
v_cache_3710_ = lean_ctor_get(v_s_3704_, 3);
v_recoveredErrors_3711_ = lean_ctor_get(v_s_3704_, 5);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_s_3704_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; lean_object* v_unused_3721_; lean_object* v_unused_3722_; 
v_unused_3720_ = lean_ctor_get(v_s_3704_, 4);
lean_dec(v_unused_3720_);
v_unused_3721_ = lean_ctor_get(v_s_3704_, 2);
lean_dec(v_unused_3721_);
v_unused_3722_ = lean_ctor_get(v_s_3704_, 1);
lean_dec(v_unused_3722_);
v___x_3713_ = v_s_3704_;
v_isShared_3714_ = v_isSharedCheck_3719_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_recoveredErrors_3711_);
lean_inc(v_cache_3710_);
lean_inc(v_stxStack_3709_);
lean_dec(v_s_3704_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3719_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3709_, v_oldStackSize_3705_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 4, v_oldError_3707_);
lean_ctor_set(v___x_3713_, 2, v_oldStopPos_3706_);
lean_ctor_set(v___x_3713_, 1, v_oldLhsPrec_3708_);
lean_ctor_set(v___x_3713_, 0, v___x_3715_);
v___x_3717_ = v___x_3713_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_oldLhsPrec_3708_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_oldStopPos_3706_);
lean_ctor_set(v_reuseFailAlloc_3718_, 3, v_cache_3710_);
lean_ctor_set(v_reuseFailAlloc_3718_, 4, v_oldError_3707_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3723_, lean_object* v_oldStackSize_3724_, lean_object* v_oldStopPos_3725_, lean_object* v_oldError_3726_, lean_object* v_oldLhsPrec_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3723_, v_oldStackSize_3724_, v_oldStopPos_3725_, v_oldError_3726_, v_oldLhsPrec_3727_);
lean_dec(v_oldStackSize_3724_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3729_, lean_object* v_oldStackSize_3730_, lean_object* v_oldError_3731_){
_start:
{
lean_object* v_stxStack_3732_; lean_object* v_lhsPrec_3733_; lean_object* v_pos_3734_; lean_object* v_cache_3735_; lean_object* v_errorMsg_3736_; lean_object* v_recoveredErrors_3737_; lean_object* v___y_3739_; 
v_stxStack_3732_ = lean_ctor_get(v_s_3729_, 0);
v_lhsPrec_3733_ = lean_ctor_get(v_s_3729_, 1);
v_pos_3734_ = lean_ctor_get(v_s_3729_, 2);
v_cache_3735_ = lean_ctor_get(v_s_3729_, 3);
v_errorMsg_3736_ = lean_ctor_get(v_s_3729_, 4);
v_recoveredErrors_3737_ = lean_ctor_get(v_s_3729_, 5);
if (lean_obj_tag(v_errorMsg_3736_) == 1)
{
lean_object* v_val_3743_; uint8_t v___x_3744_; 
lean_inc_ref(v_errorMsg_3736_);
lean_inc_ref(v_recoveredErrors_3737_);
lean_inc_ref(v_cache_3735_);
lean_inc(v_pos_3734_);
lean_inc(v_lhsPrec_3733_);
lean_inc_ref(v_stxStack_3732_);
lean_dec_ref(v_s_3729_);
v_val_3743_ = lean_ctor_get(v_errorMsg_3736_, 0);
lean_inc(v_val_3743_);
lean_dec_ref_known(v_errorMsg_3736_, 1);
v___x_3744_ = l_Lean_Parser_instBEqError_beq(v_oldError_3731_, v_val_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Parser_Error_merge(v_oldError_3731_, v_val_3743_);
v___y_3739_ = v___x_3745_;
goto v___jp_3738_;
}
else
{
lean_dec_ref(v_oldError_3731_);
v___y_3739_ = v_val_3743_;
goto v___jp_3738_;
}
}
else
{
lean_dec_ref(v_oldError_3731_);
return v_s_3729_;
}
v___jp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3740_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3732_, v_oldStackSize_3730_);
v___x_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___y_3739_);
v___x_3742_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set(v___x_3742_, 1, v_lhsPrec_3733_);
lean_ctor_set(v___x_3742_, 2, v_pos_3734_);
lean_ctor_set(v___x_3742_, 3, v_cache_3735_);
lean_ctor_set(v___x_3742_, 4, v___x_3741_);
lean_ctor_set(v___x_3742_, 5, v_recoveredErrors_3737_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3746_, lean_object* v_oldStackSize_3747_, lean_object* v_oldError_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3746_, v_oldStackSize_3747_, v_oldError_3748_);
lean_dec(v_oldStackSize_3747_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3750_, lean_object* v_startStackSize_3751_){
_start:
{
lean_object* v_stxStack_3752_; lean_object* v_lhsPrec_3753_; lean_object* v_pos_3754_; lean_object* v_cache_3755_; lean_object* v_recoveredErrors_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3765_; 
v_stxStack_3752_ = lean_ctor_get(v_s_3750_, 0);
v_lhsPrec_3753_ = lean_ctor_get(v_s_3750_, 1);
v_pos_3754_ = lean_ctor_get(v_s_3750_, 2);
v_cache_3755_ = lean_ctor_get(v_s_3750_, 3);
v_recoveredErrors_3756_ = lean_ctor_get(v_s_3750_, 5);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_s_3750_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v_s_3750_, 4);
lean_dec(v_unused_3766_);
v___x_3758_ = v_s_3750_;
v_isShared_3759_ = v_isSharedCheck_3765_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_recoveredErrors_3756_);
lean_inc(v_cache_3755_);
lean_inc(v_pos_3754_);
lean_inc(v_lhsPrec_3753_);
lean_inc(v_stxStack_3752_);
lean_dec(v_s_3750_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3765_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3760_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3752_, v_startStackSize_3751_);
v___x_3761_ = lean_box(0);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 4, v___x_3761_);
lean_ctor_set(v___x_3758_, 0, v___x_3760_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_lhsPrec_3753_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_pos_3754_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_cache_3755_);
lean_ctor_set(v_reuseFailAlloc_3764_, 4, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3764_, 5, v_recoveredErrors_3756_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3767_, lean_object* v_startStackSize_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Parser_ParserState_keepLatest(v_s_3767_, v_startStackSize_3768_);
lean_dec(v_startStackSize_3768_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3770_, lean_object* v_startStackSize_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_Parser_ParserState_keepLatest(v_s_3770_, v_startStackSize_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3773_, lean_object* v_startStackSize_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3773_, v_startStackSize_3774_);
lean_dec(v_startStackSize_3774_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3777_){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3779_ = l_Lean_Parser_ParserState_mkError(v_s_3777_, v___x_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3780_, lean_object* v_startLhsPrec_3781_, lean_object* v_p_3782_, lean_object* v_c_3783_, lean_object* v_s_3784_){
_start:
{
lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3792_; lean_object* v_s_3793_; lean_object* v_stxStack_3803_; lean_object* v_pos_3804_; lean_object* v_cache_3805_; lean_object* v_errorMsg_3806_; lean_object* v_recoveredErrors_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3820_; 
v_stxStack_3803_ = lean_ctor_get(v_s_3784_, 0);
v_pos_3804_ = lean_ctor_get(v_s_3784_, 2);
v_cache_3805_ = lean_ctor_get(v_s_3784_, 3);
v_errorMsg_3806_ = lean_ctor_get(v_s_3784_, 4);
v_recoveredErrors_3807_ = lean_ctor_get(v_s_3784_, 5);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_s_3784_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v_s_3784_, 1);
lean_dec(v_unused_3821_);
v___x_3809_ = v_s_3784_;
v_isShared_3810_ = v_isSharedCheck_3820_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_recoveredErrors_3807_);
lean_inc(v_errorMsg_3806_);
lean_inc(v_cache_3805_);
lean_inc(v_pos_3804_);
lean_inc(v_stxStack_3803_);
lean_dec(v_s_3784_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3820_;
goto v_resetjp_3808_;
}
v___jp_3785_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = l_Lean_Parser_ParserState_shrinkStack(v___y_3787_, v___y_3786_);
lean_dec(v___y_3786_);
v___x_3789_ = lean_box(0);
v___x_3790_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3788_, v___x_3789_);
return v___x_3790_;
}
v___jp_3791_:
{
lean_object* v_s_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_s_3794_ = lean_apply_2(v_p_3782_, v_c_3783_, v_s_3793_);
v___x_3795_ = l_Lean_Parser_ParserState_stackSize(v_s_3794_);
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_add(v___y_3792_, v___x_3796_);
v___x_3798_ = lean_nat_dec_eq(v___x_3795_, v___x_3797_);
lean_dec(v___x_3797_);
lean_dec(v___x_3795_);
if (v___x_3798_ == 0)
{
lean_object* v_errorMsg_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v_errorMsg_3799_ = lean_ctor_get(v_s_3794_, 4);
lean_inc(v_errorMsg_3799_);
v___x_3800_ = lean_box(0);
v___x_3801_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3799_, v___x_3800_);
lean_dec(v_errorMsg_3799_);
if (v___x_3801_ == 0)
{
v___y_3786_ = v___y_3792_;
v___y_3787_ = v_s_3794_;
goto v___jp_3785_;
}
else
{
if (v___x_3798_ == 0)
{
lean_object* v___x_3802_; 
lean_dec(v___y_3792_);
v___x_3802_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3794_);
return v___x_3802_;
}
else
{
v___y_3786_ = v___y_3792_;
v___y_3787_ = v_s_3794_;
goto v___jp_3785_;
}
}
}
else
{
lean_dec(v___y_3792_);
return v_s_3794_;
}
}
v_resetjp_3808_:
{
lean_object* v___y_3812_; 
if (lean_obj_tag(v_left_x3f_3780_) == 0)
{
lean_object* v___x_3819_; 
lean_dec(v_startLhsPrec_3781_);
v___x_3819_ = l_Lean_Parser_maxPrec;
v___y_3812_ = v___x_3819_;
goto v___jp_3811_;
}
else
{
v___y_3812_ = v_startLhsPrec_3781_;
goto v___jp_3811_;
}
v___jp_3811_:
{
lean_object* v_s_3814_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 1, v___y_3812_);
v_s_3814_ = v___x_3809_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_stxStack_3803_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___y_3812_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_pos_3804_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_cache_3805_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_errorMsg_3806_);
lean_ctor_set(v_reuseFailAlloc_3818_, 5, v_recoveredErrors_3807_);
v_s_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v_startSize_3815_; 
v_startSize_3815_ = l_Lean_Parser_ParserState_stackSize(v_s_3814_);
if (lean_obj_tag(v_left_x3f_3780_) == 1)
{
lean_object* v_val_3816_; lean_object* v_s_3817_; 
v_val_3816_ = lean_ctor_get(v_left_x3f_3780_, 0);
lean_inc(v_val_3816_);
lean_dec_ref_known(v_left_x3f_3780_, 1);
v_s_3817_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3814_, v_val_3816_);
v___y_3792_ = v_startSize_3815_;
v_s_3793_ = v_s_3817_;
goto v___jp_3791_;
}
else
{
lean_dec(v_left_x3f_3780_);
v___y_3792_ = v_startSize_3815_;
v_s_3793_ = v_s_3814_;
goto v___jp_3791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3822_, lean_object* v_prio_3823_){
_start:
{
lean_object* v_pos_3824_; lean_object* v_errorMsg_3825_; lean_object* v___y_3827_; 
v_pos_3824_ = lean_ctor_get(v_s_3822_, 2);
v_errorMsg_3825_ = lean_ctor_get(v_s_3822_, 4);
if (lean_obj_tag(v_errorMsg_3825_) == 0)
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_unsigned_to_nat(1u);
v___y_3827_ = v___x_3830_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_unsigned_to_nat(0u);
v___y_3827_ = v___x_3831_;
goto v___jp_3826_;
}
v___jp_3826_:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___y_3827_);
lean_ctor_set(v___x_3828_, 1, v_prio_3823_);
lean_inc(v_pos_3824_);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_pos_3824_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3832_, lean_object* v_prio_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3832_, v_prio_3833_);
lean_dec_ref(v_s_3832_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3835_, lean_object* v_startSize_3836_, lean_object* v_startLhsPrec_3837_, lean_object* v_startPos_3838_, lean_object* v_prevPrio_3839_, lean_object* v_prio_3840_, lean_object* v_p_3841_, lean_object* v_c_3842_, lean_object* v_s_3843_){
_start:
{
lean_object* v_lhsPrec_3844_; lean_object* v_pos_3845_; lean_object* v_errorMsg_3846_; lean_object* v_previousScore_3847_; lean_object* v_fst_3848_; lean_object* v_snd_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3905_; 
v_lhsPrec_3844_ = lean_ctor_get(v_s_3843_, 1);
lean_inc(v_lhsPrec_3844_);
v_pos_3845_ = lean_ctor_get(v_s_3843_, 2);
lean_inc(v_pos_3845_);
v_errorMsg_3846_ = lean_ctor_get(v_s_3843_, 4);
lean_inc(v_errorMsg_3846_);
lean_inc(v_prevPrio_3839_);
v_previousScore_3847_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3843_, v_prevPrio_3839_);
v_fst_3848_ = lean_ctor_get(v_previousScore_3847_, 0);
v_snd_3849_ = lean_ctor_get(v_previousScore_3847_, 1);
v_isSharedCheck_3905_ = !lean_is_exclusive(v_previousScore_3847_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3851_ = v_previousScore_3847_;
v_isShared_3852_ = v_isSharedCheck_3905_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_snd_3849_);
lean_inc(v_fst_3848_);
lean_dec(v_previousScore_3847_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3905_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_prevSize_3853_; lean_object* v_s_3854_; lean_object* v_s_3855_; lean_object* v___x_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; uint8_t v___x_3867_; 
v_prevSize_3853_ = l_Lean_Parser_ParserState_stackSize(v_s_3843_);
v_s_3854_ = l_Lean_Parser_ParserState_restore(v_s_3843_, v_prevSize_3853_, v_startPos_3838_);
v_s_3855_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3835_, v_startLhsPrec_3837_, v_p_3841_, v_c_3842_, v_s_3854_);
lean_inc(v_prio_3840_);
v___x_3864_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3855_, v_prio_3840_);
v_fst_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_fst_3865_);
v_snd_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_snd_3866_);
lean_dec_ref(v___x_3864_);
v___x_3867_ = lean_nat_dec_lt(v_fst_3848_, v_fst_3865_);
if (v___x_3867_ == 0)
{
uint8_t v___x_3868_; 
v___x_3868_ = lean_nat_dec_eq(v_fst_3848_, v_fst_3865_);
lean_dec(v_fst_3865_);
lean_dec(v_fst_3848_);
if (v___x_3868_ == 0)
{
lean_dec(v_snd_3866_);
lean_del_object(v___x_3851_);
lean_dec(v_snd_3849_);
lean_dec(v_prio_3840_);
goto v___jp_3861_;
}
else
{
lean_object* v_fst_3869_; lean_object* v_snd_3870_; lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3904_; 
v_fst_3869_ = lean_ctor_get(v_snd_3849_, 0);
lean_inc(v_fst_3869_);
v_snd_3870_ = lean_ctor_get(v_snd_3849_, 1);
lean_inc(v_snd_3870_);
lean_dec(v_snd_3849_);
v_fst_3871_ = lean_ctor_get(v_snd_3866_, 0);
v_snd_3872_ = lean_ctor_get(v_snd_3866_, 1);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_snd_3866_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3874_ = v_snd_3866_;
v_isShared_3875_ = v_isSharedCheck_3904_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_snd_3872_);
lean_inc(v_fst_3871_);
lean_dec(v_snd_3866_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3904_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_nat_dec_lt(v_fst_3869_, v_fst_3871_);
if (v___x_3876_ == 0)
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_nat_dec_eq(v_fst_3869_, v_fst_3871_);
lean_dec(v_fst_3871_);
lean_dec(v_fst_3869_);
if (v___x_3877_ == 0)
{
lean_del_object(v___x_3874_);
lean_dec(v_snd_3872_);
lean_dec(v_snd_3870_);
lean_del_object(v___x_3851_);
lean_dec(v_prio_3840_);
goto v___jp_3861_;
}
else
{
uint8_t v___x_3878_; 
v___x_3878_ = lean_nat_dec_lt(v_snd_3870_, v_snd_3872_);
if (v___x_3878_ == 0)
{
uint8_t v___x_3879_; 
lean_del_object(v___x_3851_);
v___x_3879_ = lean_nat_dec_eq(v_snd_3870_, v_snd_3872_);
lean_dec(v_snd_3872_);
lean_dec(v_snd_3870_);
if (v___x_3879_ == 0)
{
lean_del_object(v___x_3874_);
lean_dec(v_prio_3840_);
goto v___jp_3861_;
}
else
{
lean_dec(v_pos_3845_);
lean_dec(v_prevPrio_3839_);
if (lean_obj_tag(v_errorMsg_3846_) == 0)
{
lean_object* v_stxStack_3880_; lean_object* v_lhsPrec_3881_; lean_object* v_pos_3882_; lean_object* v_cache_3883_; lean_object* v_errorMsg_3884_; lean_object* v_recoveredErrors_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_prevSize_3853_);
v_stxStack_3880_ = lean_ctor_get(v_s_3855_, 0);
v_lhsPrec_3881_ = lean_ctor_get(v_s_3855_, 1);
v_pos_3882_ = lean_ctor_get(v_s_3855_, 2);
v_cache_3883_ = lean_ctor_get(v_s_3855_, 3);
v_errorMsg_3884_ = lean_ctor_get(v_s_3855_, 4);
v_recoveredErrors_3885_ = lean_ctor_get(v_s_3855_, 5);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_s_3855_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3887_ = v_s_3855_;
v_isShared_3888_ = v_isSharedCheck_3898_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_recoveredErrors_3885_);
lean_inc(v_errorMsg_3884_);
lean_inc(v_cache_3883_);
lean_inc(v_pos_3882_);
lean_inc(v_lhsPrec_3881_);
lean_inc(v_stxStack_3880_);
lean_dec(v_s_3855_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3898_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___y_3890_; uint8_t v___x_3897_; 
v___x_3897_ = lean_nat_dec_le(v_lhsPrec_3881_, v_lhsPrec_3844_);
if (v___x_3897_ == 0)
{
lean_dec(v_lhsPrec_3881_);
v___y_3890_ = v_lhsPrec_3844_;
goto v___jp_3889_;
}
else
{
lean_dec(v_lhsPrec_3844_);
v___y_3890_ = v_lhsPrec_3881_;
goto v___jp_3889_;
}
v___jp_3889_:
{
lean_object* v___x_3892_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v___y_3890_);
v___x_3892_ = v___x_3887_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_stxStack_3880_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___y_3890_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_pos_3882_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v_cache_3883_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v_errorMsg_3884_);
lean_ctor_set(v_reuseFailAlloc_3896_, 5, v_recoveredErrors_3885_);
v___x_3892_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3894_; 
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 1, v_prio_3840_);
lean_ctor_set(v___x_3874_, 0, v___x_3892_);
v___x_3894_ = v___x_3874_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_prio_3840_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
lean_dec(v_lhsPrec_3844_);
v_val_3899_ = lean_ctor_get(v_errorMsg_3846_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_errorMsg_3846_, 1);
v___x_3900_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3855_, v_prevSize_3853_, v_val_3899_);
lean_dec(v_prevSize_3853_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 1, v_prio_3840_);
lean_ctor_set(v___x_3874_, 0, v___x_3900_);
v___x_3902_ = v___x_3874_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_prio_3840_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_del_object(v___x_3874_);
lean_dec(v_snd_3872_);
lean_dec(v_snd_3870_);
lean_dec(v_prevSize_3853_);
lean_dec(v_errorMsg_3846_);
lean_dec(v_pos_3845_);
lean_dec(v_lhsPrec_3844_);
lean_dec(v_prevPrio_3839_);
goto v___jp_3856_;
}
}
}
else
{
lean_del_object(v___x_3874_);
lean_dec(v_snd_3872_);
lean_dec(v_fst_3871_);
lean_dec(v_snd_3870_);
lean_dec(v_fst_3869_);
lean_dec(v_prevSize_3853_);
lean_dec(v_errorMsg_3846_);
lean_dec(v_pos_3845_);
lean_dec(v_lhsPrec_3844_);
lean_dec(v_prevPrio_3839_);
goto v___jp_3856_;
}
}
}
}
else
{
lean_dec(v_snd_3866_);
lean_dec(v_fst_3865_);
lean_dec(v_prevSize_3853_);
lean_dec(v_snd_3849_);
lean_dec(v_fst_3848_);
lean_dec(v_errorMsg_3846_);
lean_dec(v_pos_3845_);
lean_dec(v_lhsPrec_3844_);
lean_dec(v_prevPrio_3839_);
goto v___jp_3856_;
}
v___jp_3856_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3857_ = l_Lean_Parser_ParserState_keepNewError(v_s_3855_, v_startSize_3836_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 1, v_prio_3840_);
lean_ctor_set(v___x_3851_, 0, v___x_3857_);
v___x_3859_ = v___x_3851_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_prio_3840_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
v___jp_3861_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3855_, v_prevSize_3853_, v_pos_3845_, v_errorMsg_3846_, v_lhsPrec_3844_);
lean_dec(v_prevSize_3853_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v_prevPrio_3839_);
return v___x_3863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3906_, lean_object* v_startSize_3907_, lean_object* v_startLhsPrec_3908_, lean_object* v_startPos_3909_, lean_object* v_prevPrio_3910_, lean_object* v_prio_3911_, lean_object* v_p_3912_, lean_object* v_c_3913_, lean_object* v_s_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3906_, v_startSize_3907_, v_startLhsPrec_3908_, v_startPos_3909_, v_prevPrio_3910_, v_prio_3911_, v_p_3912_, v_c_3913_, v_s_3914_);
lean_dec(v_startSize_3907_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3916_, lean_object* v_s_3917_){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = lean_nat_add(v_startSize_3916_, v___x_3918_);
v___x_3920_ = l_Lean_Parser_ParserState_stackSize(v_s_3917_);
v___x_3921_ = lean_nat_dec_lt(v___x_3919_, v___x_3920_);
lean_dec(v___x_3920_);
lean_dec(v___x_3919_);
if (v___x_3921_ == 0)
{
return v_s_3917_;
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3923_ = l_Lean_Parser_ParserState_mkNode(v_s_3917_, v___x_3922_, v_startSize_3916_);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3924_, lean_object* v_s_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3924_, v_s_3925_);
lean_dec(v_startSize_3924_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3927_, lean_object* v_startSize_3928_, lean_object* v_startLhsPrec_3929_, lean_object* v_startPos_3930_, lean_object* v_prevPrio_3931_, lean_object* v_ps_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
if (lean_obj_tag(v_ps_3932_) == 0)
{
lean_object* v___x_3935_; 
lean_dec_ref(v_a_3933_);
lean_dec(v_prevPrio_3931_);
lean_dec(v_startPos_3930_);
lean_dec(v_startLhsPrec_3929_);
lean_dec(v_left_x3f_3927_);
v___x_3935_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3928_, v_a_3934_);
return v___x_3935_;
}
else
{
lean_object* v_head_3936_; lean_object* v_fst_3937_; lean_object* v_tail_3938_; lean_object* v_snd_3939_; lean_object* v_fn_3940_; lean_object* v___x_3941_; lean_object* v_fst_3942_; lean_object* v_snd_3943_; 
v_head_3936_ = lean_ctor_get(v_ps_3932_, 0);
lean_inc(v_head_3936_);
v_fst_3937_ = lean_ctor_get(v_head_3936_, 0);
lean_inc(v_fst_3937_);
v_tail_3938_ = lean_ctor_get(v_ps_3932_, 1);
lean_inc(v_tail_3938_);
lean_dec_ref_known(v_ps_3932_, 2);
v_snd_3939_ = lean_ctor_get(v_head_3936_, 1);
lean_inc(v_snd_3939_);
lean_dec(v_head_3936_);
v_fn_3940_ = lean_ctor_get(v_fst_3937_, 1);
lean_inc_ref(v_fn_3940_);
lean_dec(v_fst_3937_);
lean_inc_ref(v_a_3933_);
lean_inc(v_startPos_3930_);
lean_inc(v_startLhsPrec_3929_);
lean_inc(v_left_x3f_3927_);
v___x_3941_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3927_, v_startSize_3928_, v_startLhsPrec_3929_, v_startPos_3930_, v_prevPrio_3931_, v_snd_3939_, v_fn_3940_, v_a_3933_, v_a_3934_);
v_fst_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_fst_3942_);
v_snd_3943_ = lean_ctor_get(v___x_3941_, 1);
lean_inc(v_snd_3943_);
lean_dec_ref(v___x_3941_);
v_prevPrio_3931_ = v_snd_3943_;
v_ps_3932_ = v_tail_3938_;
v_a_3934_ = v_fst_3942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3945_, lean_object* v_startSize_3946_, lean_object* v_startLhsPrec_3947_, lean_object* v_startPos_3948_, lean_object* v_prevPrio_3949_, lean_object* v_ps_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3945_, v_startSize_3946_, v_startLhsPrec_3947_, v_startPos_3948_, v_prevPrio_3949_, v_ps_3950_, v_a_3951_, v_a_3952_);
lean_dec(v_startSize_3946_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3954_, lean_object* v_startSize_3955_, lean_object* v_startLhsPrec_3956_, lean_object* v_startPos_3957_, lean_object* v_prevPrio_3958_, lean_object* v_ps_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3954_, v_startSize_3955_, v_startLhsPrec_3956_, v_startPos_3957_, v_prevPrio_3958_, v_ps_3959_, v_a_3960_, v_a_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3963_, lean_object* v_startSize_3964_, lean_object* v_startLhsPrec_3965_, lean_object* v_startPos_3966_, lean_object* v_prevPrio_3967_, lean_object* v_ps_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3963_, v_startSize_3964_, v_startLhsPrec_3965_, v_startPos_3966_, v_prevPrio_3967_, v_ps_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_startSize_3964_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3973_, lean_object* v_x_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
if (lean_obj_tag(v_x_3974_) == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec_ref(v_a_3975_);
lean_dec(v_left_x3f_3973_);
v___x_3977_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3978_ = l_Lean_Parser_ParserState_mkError(v_a_3976_, v___x_3977_);
return v___x_3978_;
}
else
{
lean_object* v_tail_3979_; 
v_tail_3979_ = lean_ctor_get(v_x_3974_, 1);
if (lean_obj_tag(v_tail_3979_) == 0)
{
lean_object* v_head_3980_; lean_object* v_fst_3981_; lean_object* v_lhsPrec_3982_; lean_object* v_fn_3983_; lean_object* v___x_3984_; 
v_head_3980_ = lean_ctor_get(v_x_3974_, 0);
lean_inc(v_head_3980_);
lean_dec_ref_known(v_x_3974_, 2);
v_fst_3981_ = lean_ctor_get(v_head_3980_, 0);
lean_inc(v_fst_3981_);
lean_dec(v_head_3980_);
v_lhsPrec_3982_ = lean_ctor_get(v_a_3976_, 1);
lean_inc(v_lhsPrec_3982_);
v_fn_3983_ = lean_ctor_get(v_fst_3981_, 1);
lean_inc_ref(v_fn_3983_);
lean_dec(v_fst_3981_);
v___x_3984_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3973_, v_lhsPrec_3982_, v_fn_3983_, v_a_3975_, v_a_3976_);
return v___x_3984_;
}
else
{
lean_object* v_head_3985_; lean_object* v_fst_3986_; lean_object* v_lhsPrec_3987_; lean_object* v_pos_3988_; lean_object* v_snd_3989_; lean_object* v_fn_3990_; lean_object* v_startSize_3991_; lean_object* v_s_3992_; lean_object* v___x_3993_; 
lean_inc(v_tail_3979_);
v_head_3985_ = lean_ctor_get(v_x_3974_, 0);
lean_inc(v_head_3985_);
lean_dec_ref_known(v_x_3974_, 2);
v_fst_3986_ = lean_ctor_get(v_head_3985_, 0);
lean_inc(v_fst_3986_);
v_lhsPrec_3987_ = lean_ctor_get(v_a_3976_, 1);
lean_inc_n(v_lhsPrec_3987_, 2);
v_pos_3988_ = lean_ctor_get(v_a_3976_, 2);
lean_inc(v_pos_3988_);
v_snd_3989_ = lean_ctor_get(v_head_3985_, 1);
lean_inc(v_snd_3989_);
lean_dec(v_head_3985_);
v_fn_3990_ = lean_ctor_get(v_fst_3986_, 1);
lean_inc_ref(v_fn_3990_);
lean_dec(v_fst_3986_);
v_startSize_3991_ = l_Lean_Parser_ParserState_stackSize(v_a_3976_);
lean_inc_ref(v_a_3975_);
lean_inc(v_left_x3f_3973_);
v_s_3992_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3973_, v_lhsPrec_3987_, v_fn_3990_, v_a_3975_, v_a_3976_);
v___x_3993_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3973_, v_startSize_3991_, v_lhsPrec_3987_, v_pos_3988_, v_snd_3989_, v_tail_3979_, v_a_3975_, v_s_3992_);
lean_dec(v_startSize_3991_);
return v___x_3993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_3995_, lean_object* v_x_3996_, lean_object* v_x_3997_){
_start:
{
if (lean_obj_tag(v_x_3995_) == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_dec_ref(v_x_3996_);
v___x_3998_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_3999_ = l_Lean_Parser_ParserState_mkError(v_x_3997_, v___x_3998_);
return v___x_3999_;
}
else
{
lean_object* v_tail_4000_; 
v_tail_4000_ = lean_ctor_get(v_x_3995_, 1);
if (lean_obj_tag(v_tail_4000_) == 0)
{
lean_object* v_head_4001_; lean_object* v_fn_4002_; lean_object* v___x_4003_; 
v_head_4001_ = lean_ctor_get(v_x_3995_, 0);
lean_inc(v_head_4001_);
lean_dec_ref_known(v_x_3995_, 2);
v_fn_4002_ = lean_ctor_get(v_head_4001_, 1);
lean_inc_ref(v_fn_4002_);
lean_dec(v_head_4001_);
v___x_4003_ = lean_apply_2(v_fn_4002_, v_x_3996_, v_x_3997_);
return v___x_4003_;
}
else
{
lean_object* v_head_4004_; lean_object* v_fn_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_inc(v_tail_4000_);
v_head_4004_ = lean_ctor_get(v_x_3995_, 0);
lean_inc(v_head_4004_);
lean_dec_ref_known(v_x_3995_, 2);
v_fn_4005_ = lean_ctor_get(v_head_4004_, 1);
lean_inc_ref(v_fn_4005_);
lean_dec(v_head_4004_);
v___x_4006_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_4006_, 0, v_tail_4000_);
v___x_4007_ = l_Lean_Parser_orelseFn(v_fn_4005_, v___x_4006_, v_x_3996_, v_x_3997_);
return v___x_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_4008_, lean_object* v_c_4009_, lean_object* v_s_4010_){
_start:
{
lean_object* v_toCacheableParserContext_4011_; lean_object* v_savedPos_x3f_4012_; 
v_toCacheableParserContext_4011_ = lean_ctor_get(v_c_4009_, 2);
v_savedPos_x3f_4012_ = lean_ctor_get(v_toCacheableParserContext_4011_, 2);
lean_inc(v_savedPos_x3f_4012_);
if (lean_obj_tag(v_savedPos_x3f_4012_) == 0)
{
lean_dec_ref(v_c_4009_);
lean_dec_ref(v_errorMsg_4008_);
return v_s_4010_;
}
else
{
lean_object* v_toInputContext_4013_; lean_object* v_val_4014_; lean_object* v_fileMap_4015_; lean_object* v_pos_4016_; lean_object* v_savedPos_4017_; lean_object* v_pos_4018_; lean_object* v_column_4019_; lean_object* v_column_4020_; uint8_t v___x_4021_; 
v_toInputContext_4013_ = lean_ctor_get(v_c_4009_, 0);
lean_inc_ref(v_toInputContext_4013_);
lean_dec_ref(v_c_4009_);
v_val_4014_ = lean_ctor_get(v_savedPos_x3f_4012_, 0);
lean_inc(v_val_4014_);
lean_dec_ref_known(v_savedPos_x3f_4012_, 1);
v_fileMap_4015_ = lean_ctor_get(v_toInputContext_4013_, 2);
lean_inc_ref_n(v_fileMap_4015_, 2);
lean_dec_ref(v_toInputContext_4013_);
v_pos_4016_ = lean_ctor_get(v_s_4010_, 2);
v_savedPos_4017_ = l_Lean_FileMap_toPosition(v_fileMap_4015_, v_val_4014_);
lean_dec(v_val_4014_);
v_pos_4018_ = l_Lean_FileMap_toPosition(v_fileMap_4015_, v_pos_4016_);
v_column_4019_ = lean_ctor_get(v_pos_4018_, 1);
lean_inc(v_column_4019_);
lean_dec_ref(v_pos_4018_);
v_column_4020_ = lean_ctor_get(v_savedPos_4017_, 1);
lean_inc(v_column_4020_);
lean_dec_ref(v_savedPos_4017_);
v___x_4021_ = lean_nat_dec_eq(v_column_4019_, v_column_4020_);
lean_dec(v_column_4020_);
lean_dec(v_column_4019_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_Parser_ParserState_mkError(v_s_4010_, v_errorMsg_4008_);
return v___x_4022_;
}
else
{
lean_dec_ref(v_errorMsg_4008_);
return v_s_4010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_4023_){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4025_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_4025_, 0, v_errorMsg_4023_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4035_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4036_ = l_Lean_addBuiltinDocString(v___x_4034_, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4039_, lean_object* v_c_4040_, lean_object* v_s_4041_){
_start:
{
lean_object* v_toCacheableParserContext_4042_; lean_object* v_savedPos_x3f_4043_; 
v_toCacheableParserContext_4042_ = lean_ctor_get(v_c_4040_, 2);
v_savedPos_x3f_4043_ = lean_ctor_get(v_toCacheableParserContext_4042_, 2);
lean_inc(v_savedPos_x3f_4043_);
if (lean_obj_tag(v_savedPos_x3f_4043_) == 0)
{
lean_dec_ref(v_c_4040_);
lean_dec_ref(v_errorMsg_4039_);
return v_s_4041_;
}
else
{
lean_object* v_toInputContext_4044_; lean_object* v_val_4045_; lean_object* v_fileMap_4046_; lean_object* v_pos_4047_; lean_object* v_savedPos_4048_; lean_object* v_column_4049_; lean_object* v_pos_4050_; lean_object* v_column_4051_; uint8_t v___x_4052_; 
v_toInputContext_4044_ = lean_ctor_get(v_c_4040_, 0);
lean_inc_ref(v_toInputContext_4044_);
lean_dec_ref(v_c_4040_);
v_val_4045_ = lean_ctor_get(v_savedPos_x3f_4043_, 0);
lean_inc(v_val_4045_);
lean_dec_ref_known(v_savedPos_x3f_4043_, 1);
v_fileMap_4046_ = lean_ctor_get(v_toInputContext_4044_, 2);
lean_inc_ref_n(v_fileMap_4046_, 2);
lean_dec_ref(v_toInputContext_4044_);
v_pos_4047_ = lean_ctor_get(v_s_4041_, 2);
v_savedPos_4048_ = l_Lean_FileMap_toPosition(v_fileMap_4046_, v_val_4045_);
lean_dec(v_val_4045_);
v_column_4049_ = lean_ctor_get(v_savedPos_4048_, 1);
lean_inc(v_column_4049_);
lean_dec_ref(v_savedPos_4048_);
v_pos_4050_ = l_Lean_FileMap_toPosition(v_fileMap_4046_, v_pos_4047_);
v_column_4051_ = lean_ctor_get(v_pos_4050_, 1);
lean_inc(v_column_4051_);
lean_dec_ref(v_pos_4050_);
v___x_4052_ = lean_nat_dec_le(v_column_4049_, v_column_4051_);
lean_dec(v_column_4051_);
lean_dec(v_column_4049_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Parser_ParserState_mkError(v_s_4041_, v_errorMsg_4039_);
return v___x_4053_;
}
else
{
lean_dec_ref(v_errorMsg_4039_);
return v_s_4041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4054_){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4056_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4056_, 0, v_errorMsg_4054_);
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4066_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4067_ = l_Lean_addBuiltinDocString(v___x_4065_, v___x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4070_, lean_object* v_c_4071_, lean_object* v_s_4072_){
_start:
{
lean_object* v_toCacheableParserContext_4073_; lean_object* v_savedPos_x3f_4074_; 
v_toCacheableParserContext_4073_ = lean_ctor_get(v_c_4071_, 2);
v_savedPos_x3f_4074_ = lean_ctor_get(v_toCacheableParserContext_4073_, 2);
lean_inc(v_savedPos_x3f_4074_);
if (lean_obj_tag(v_savedPos_x3f_4074_) == 0)
{
lean_dec_ref(v_c_4071_);
lean_dec_ref(v_errorMsg_4070_);
return v_s_4072_;
}
else
{
lean_object* v_toInputContext_4075_; lean_object* v_val_4076_; lean_object* v_fileMap_4077_; lean_object* v_pos_4078_; lean_object* v_savedPos_4079_; lean_object* v_column_4080_; lean_object* v_pos_4081_; lean_object* v_column_4082_; uint8_t v___x_4083_; 
v_toInputContext_4075_ = lean_ctor_get(v_c_4071_, 0);
lean_inc_ref(v_toInputContext_4075_);
lean_dec_ref(v_c_4071_);
v_val_4076_ = lean_ctor_get(v_savedPos_x3f_4074_, 0);
lean_inc(v_val_4076_);
lean_dec_ref_known(v_savedPos_x3f_4074_, 1);
v_fileMap_4077_ = lean_ctor_get(v_toInputContext_4075_, 2);
lean_inc_ref_n(v_fileMap_4077_, 2);
lean_dec_ref(v_toInputContext_4075_);
v_pos_4078_ = lean_ctor_get(v_s_4072_, 2);
v_savedPos_4079_ = l_Lean_FileMap_toPosition(v_fileMap_4077_, v_val_4076_);
lean_dec(v_val_4076_);
v_column_4080_ = lean_ctor_get(v_savedPos_4079_, 1);
lean_inc(v_column_4080_);
lean_dec_ref(v_savedPos_4079_);
v_pos_4081_ = l_Lean_FileMap_toPosition(v_fileMap_4077_, v_pos_4078_);
v_column_4082_ = lean_ctor_get(v_pos_4081_, 1);
lean_inc(v_column_4082_);
lean_dec_ref(v_pos_4081_);
v___x_4083_ = lean_nat_dec_lt(v_column_4080_, v_column_4082_);
lean_dec(v_column_4082_);
lean_dec(v_column_4080_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Parser_ParserState_mkError(v_s_4072_, v_errorMsg_4070_);
return v___x_4084_;
}
else
{
lean_dec_ref(v_errorMsg_4070_);
return v_s_4072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4085_){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4087_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4087_, 0, v_errorMsg_4085_);
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4097_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4098_ = l_Lean_addBuiltinDocString(v___x_4096_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4101_, lean_object* v_c_4102_, lean_object* v_s_4103_){
_start:
{
lean_object* v_toCacheableParserContext_4104_; lean_object* v_savedPos_x3f_4105_; 
v_toCacheableParserContext_4104_ = lean_ctor_get(v_c_4102_, 2);
v_savedPos_x3f_4105_ = lean_ctor_get(v_toCacheableParserContext_4104_, 2);
lean_inc(v_savedPos_x3f_4105_);
if (lean_obj_tag(v_savedPos_x3f_4105_) == 0)
{
lean_dec_ref(v_c_4102_);
lean_dec_ref(v_errorMsg_4101_);
return v_s_4103_;
}
else
{
lean_object* v_toInputContext_4106_; lean_object* v_val_4107_; lean_object* v_fileMap_4108_; lean_object* v_pos_4109_; lean_object* v_savedPos_4110_; lean_object* v_pos_4111_; lean_object* v_line_4112_; lean_object* v_line_4113_; uint8_t v___x_4114_; 
v_toInputContext_4106_ = lean_ctor_get(v_c_4102_, 0);
lean_inc_ref(v_toInputContext_4106_);
lean_dec_ref(v_c_4102_);
v_val_4107_ = lean_ctor_get(v_savedPos_x3f_4105_, 0);
lean_inc(v_val_4107_);
lean_dec_ref_known(v_savedPos_x3f_4105_, 1);
v_fileMap_4108_ = lean_ctor_get(v_toInputContext_4106_, 2);
lean_inc_ref_n(v_fileMap_4108_, 2);
lean_dec_ref(v_toInputContext_4106_);
v_pos_4109_ = lean_ctor_get(v_s_4103_, 2);
v_savedPos_4110_ = l_Lean_FileMap_toPosition(v_fileMap_4108_, v_val_4107_);
lean_dec(v_val_4107_);
v_pos_4111_ = l_Lean_FileMap_toPosition(v_fileMap_4108_, v_pos_4109_);
v_line_4112_ = lean_ctor_get(v_pos_4111_, 0);
lean_inc(v_line_4112_);
lean_dec_ref(v_pos_4111_);
v_line_4113_ = lean_ctor_get(v_savedPos_4110_, 0);
lean_inc(v_line_4113_);
lean_dec_ref(v_savedPos_4110_);
v___x_4114_ = lean_nat_dec_eq(v_line_4112_, v_line_4113_);
lean_dec(v_line_4113_);
lean_dec(v_line_4112_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_Parser_ParserState_mkError(v_s_4103_, v_errorMsg_4101_);
return v___x_4115_;
}
else
{
lean_dec_ref(v_errorMsg_4101_);
return v_s_4103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4116_){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4118_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4118_, 0, v_errorMsg_4116_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4117_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4128_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4129_ = l_Lean_addBuiltinDocString(v___x_4127_, v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4132_, lean_object* v_x_4133_){
_start:
{
lean_object* v_prec_4134_; lean_object* v_quotDepth_4135_; uint8_t v_suppressInsideQuot_4136_; lean_object* v_forbiddenTks_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4146_; 
v_prec_4134_ = lean_ctor_get(v_x_4133_, 0);
v_quotDepth_4135_ = lean_ctor_get(v_x_4133_, 1);
v_suppressInsideQuot_4136_ = lean_ctor_get_uint8(v_x_4133_, sizeof(void*)*4);
v_forbiddenTks_4137_ = lean_ctor_get(v_x_4133_, 3);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_x_4133_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_x_4133_, 2);
lean_dec(v_unused_4147_);
v___x_4139_ = v_x_4133_;
v_isShared_4140_ = v_isSharedCheck_4146_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_forbiddenTks_4137_);
lean_inc(v_quotDepth_4135_);
lean_inc(v_prec_4134_);
lean_dec(v_x_4133_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4146_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v_pos_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v_pos_4141_ = lean_ctor_get(v___y_4132_, 2);
lean_inc(v_pos_4141_);
v___x_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_pos_4141_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 2, v___x_4142_);
v___x_4144_ = v___x_4139_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_prec_4134_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_quotDepth_4135_);
lean_ctor_set(v_reuseFailAlloc_4145_, 2, v___x_4142_);
lean_ctor_set(v_reuseFailAlloc_4145_, 3, v_forbiddenTks_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4145_, sizeof(void*)*4, v_suppressInsideQuot_4136_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4148_, lean_object* v_x_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_Parser_withPosition___lam__0(v___y_4148_, v_x_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___f_4154_; lean_object* v___x_4155_; 
lean_inc_ref(v___y_4153_);
v___f_4154_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4154_, 0, v___y_4153_);
v___x_4155_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4154_, v_fn_4151_, v___y_4152_, v___y_4153_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4156_){
_start:
{
lean_object* v_info_4157_; lean_object* v_fn_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4166_; 
v_info_4157_ = lean_ctor_get(v_p_4156_, 0);
v_fn_4158_ = lean_ctor_get(v_p_4156_, 1);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_p_4156_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4160_ = v_p_4156_;
v_isShared_4161_ = v_isSharedCheck_4166_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_fn_4158_);
lean_inc(v_info_4157_);
lean_dec(v_p_4156_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4166_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___f_4162_; lean_object* v___x_4164_; 
v___f_4162_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4162_, 0, v_fn_4158_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 1, v___f_4162_);
v___x_4164_ = v___x_4160_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_info_4157_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v___f_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4174_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4175_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4176_ = l_Lean_addBuiltinDocString(v___x_4174_, v___x_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4179_, lean_object* v_pos_4180_, lean_object* v_c_4181_){
_start:
{
uint8_t v___x_4182_; 
v___x_4182_ = l_Lean_Parser_checkTailLinebreak(v_prev_4179_);
if (v___x_4182_ == 0)
{
lean_dec(v_pos_4180_);
return v_c_4181_;
}
else
{
lean_object* v_prec_4183_; lean_object* v_quotDepth_4184_; uint8_t v_suppressInsideQuot_4185_; lean_object* v_forbiddenTks_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4194_; 
v_prec_4183_ = lean_ctor_get(v_c_4181_, 0);
v_quotDepth_4184_ = lean_ctor_get(v_c_4181_, 1);
v_suppressInsideQuot_4185_ = lean_ctor_get_uint8(v_c_4181_, sizeof(void*)*4);
v_forbiddenTks_4186_ = lean_ctor_get(v_c_4181_, 3);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_c_4181_);
if (v_isSharedCheck_4194_ == 0)
{
lean_object* v_unused_4195_; 
v_unused_4195_ = lean_ctor_get(v_c_4181_, 2);
lean_dec(v_unused_4195_);
v___x_4188_ = v_c_4181_;
v_isShared_4189_ = v_isSharedCheck_4194_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_forbiddenTks_4186_);
lean_inc(v_quotDepth_4184_);
lean_inc(v_prec_4183_);
lean_dec(v_c_4181_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4194_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
v___x_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4190_, 0, v_pos_4180_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 2, v___x_4190_);
v___x_4192_ = v___x_4188_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_prec_4183_);
lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_quotDepth_4184_);
lean_ctor_set(v_reuseFailAlloc_4193_, 2, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4193_, 3, v_forbiddenTks_4186_);
lean_ctor_set_uint8(v_reuseFailAlloc_4193_, sizeof(void*)*4, v_suppressInsideQuot_4185_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4196_, lean_object* v_pos_4197_, lean_object* v_c_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4196_, v_pos_4197_, v_c_4198_);
lean_dec(v_prev_4196_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_stxStack_4203_; lean_object* v_pos_4204_; lean_object* v_prev_4205_; lean_object* v___f_4206_; lean_object* v___x_4207_; 
v_stxStack_4203_ = lean_ctor_get(v___y_4202_, 0);
v_pos_4204_ = lean_ctor_get(v___y_4202_, 2);
v_prev_4205_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4203_);
lean_inc(v_pos_4204_);
v___f_4206_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4206_, 0, v_prev_4205_);
lean_closure_set(v___f_4206_, 1, v_pos_4204_);
v___x_4207_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4206_, v_fn_4200_, v___y_4201_, v___y_4202_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4208_){
_start:
{
lean_object* v_info_4209_; lean_object* v_fn_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4218_; 
v_info_4209_ = lean_ctor_get(v_p_4208_, 0);
v_fn_4210_ = lean_ctor_get(v_p_4208_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_p_4208_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4212_ = v_p_4208_;
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_fn_4210_);
lean_inc(v_info_4209_);
lean_dec(v_p_4208_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___f_4214_; lean_object* v___x_4216_; 
v___f_4214_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4214_, 0, v_fn_4210_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 1, v___f_4214_);
v___x_4216_ = v___x_4212_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_info_4209_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v___f_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4219_){
_start:
{
lean_object* v_prec_4220_; lean_object* v_quotDepth_4221_; uint8_t v_suppressInsideQuot_4222_; lean_object* v_forbiddenTks_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4231_; 
v_prec_4220_ = lean_ctor_get(v_x_4219_, 0);
v_quotDepth_4221_ = lean_ctor_get(v_x_4219_, 1);
v_suppressInsideQuot_4222_ = lean_ctor_get_uint8(v_x_4219_, sizeof(void*)*4);
v_forbiddenTks_4223_ = lean_ctor_get(v_x_4219_, 3);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_x_4219_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v_x_4219_, 2);
lean_dec(v_unused_4232_);
v___x_4225_ = v_x_4219_;
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_forbiddenTks_4223_);
lean_inc(v_quotDepth_4221_);
lean_inc(v_prec_4220_);
lean_dec(v_x_4219_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4227_ = lean_box(0);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 2, v___x_4227_);
v___x_4229_ = v___x_4225_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_prec_4220_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_quotDepth_4221_);
lean_ctor_set(v_reuseFailAlloc_4230_, 2, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4230_, 3, v_forbiddenTks_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4230_, sizeof(void*)*4, v_suppressInsideQuot_4222_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4234_){
_start:
{
lean_object* v___f_4235_; lean_object* v___x_4236_; 
v___f_4235_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4236_ = l_Lean_Parser_adaptCacheableContext(v___f_4235_, v_p_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4245_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4246_ = l_Lean_addBuiltinDocString(v___x_4244_, v___x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4249_, lean_object* v_c_4250_){
_start:
{
lean_object* v_prec_4251_; lean_object* v_quotDepth_4252_; uint8_t v_suppressInsideQuot_4253_; lean_object* v_savedPos_x3f_4254_; lean_object* v_forbiddenTks_4255_; uint8_t v___x_4256_; 
v_prec_4251_ = lean_ctor_get(v_c_4250_, 0);
v_quotDepth_4252_ = lean_ctor_get(v_c_4250_, 1);
v_suppressInsideQuot_4253_ = lean_ctor_get_uint8(v_c_4250_, sizeof(void*)*4);
v_savedPos_x3f_4254_ = lean_ctor_get(v_c_4250_, 2);
v_forbiddenTks_4255_ = lean_ctor_get(v_c_4250_, 3);
v___x_4256_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_4255_, v_tk_4249_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4264_; 
lean_inc_ref(v_forbiddenTks_4255_);
lean_inc(v_savedPos_x3f_4254_);
lean_inc(v_quotDepth_4252_);
lean_inc(v_prec_4251_);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_c_4250_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; lean_object* v_unused_4266_; lean_object* v_unused_4267_; lean_object* v_unused_4268_; 
v_unused_4265_ = lean_ctor_get(v_c_4250_, 3);
lean_dec(v_unused_4265_);
v_unused_4266_ = lean_ctor_get(v_c_4250_, 2);
lean_dec(v_unused_4266_);
v_unused_4267_ = lean_ctor_get(v_c_4250_, 1);
lean_dec(v_unused_4267_);
v_unused_4268_ = lean_ctor_get(v_c_4250_, 0);
lean_dec(v_unused_4268_);
v___x_4258_ = v_c_4250_;
v_isShared_4259_ = v_isSharedCheck_4264_;
goto v_resetjp_4257_;
}
else
{
lean_dec(v_c_4250_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4264_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4260_ = lean_array_push(v_forbiddenTks_4255_, v_tk_4249_);
if (v_isShared_4259_ == 0)
{
lean_ctor_set(v___x_4258_, 3, v___x_4260_);
v___x_4262_ = v___x_4258_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_prec_4251_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_quotDepth_4252_);
lean_ctor_set(v_reuseFailAlloc_4263_, 2, v_savedPos_x3f_4254_);
lean_ctor_set(v_reuseFailAlloc_4263_, 3, v___x_4260_);
lean_ctor_set_uint8(v_reuseFailAlloc_4263_, sizeof(void*)*4, v_suppressInsideQuot_4253_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
else
{
lean_dec_ref(v_tk_4249_);
return v_c_4250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4269_, lean_object* v_p_4270_){
_start:
{
lean_object* v___f_4271_; lean_object* v___x_4272_; 
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4271_, 0, v_tk_4269_);
v___x_4272_ = l_Lean_Parser_adaptCacheableContext(v___f_4271_, v_p_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4280_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4281_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4282_ = l_Lean_addBuiltinDocString(v___x_4280_, v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4287_){
_start:
{
lean_object* v_prec_4288_; lean_object* v_quotDepth_4289_; uint8_t v_suppressInsideQuot_4290_; lean_object* v_savedPos_x3f_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4299_; 
v_prec_4288_ = lean_ctor_get(v_x_4287_, 0);
v_quotDepth_4289_ = lean_ctor_get(v_x_4287_, 1);
v_suppressInsideQuot_4290_ = lean_ctor_get_uint8(v_x_4287_, sizeof(void*)*4);
v_savedPos_x3f_4291_ = lean_ctor_get(v_x_4287_, 2);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_x_4287_);
if (v_isSharedCheck_4299_ == 0)
{
lean_object* v_unused_4300_; 
v_unused_4300_ = lean_ctor_get(v_x_4287_, 3);
lean_dec(v_unused_4300_);
v___x_4293_ = v_x_4287_;
v_isShared_4294_ = v_isSharedCheck_4299_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_savedPos_x3f_4291_);
lean_inc(v_quotDepth_4289_);
lean_inc(v_prec_4288_);
lean_dec(v_x_4287_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4299_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
v___x_4295_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___lam__0___closed__0));
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 3, v___x_4295_);
v___x_4297_ = v___x_4293_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_prec_4288_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_quotDepth_4289_);
lean_ctor_set(v_reuseFailAlloc_4298_, 2, v_savedPos_x3f_4291_);
lean_ctor_set(v_reuseFailAlloc_4298_, 3, v___x_4295_);
lean_ctor_set_uint8(v_reuseFailAlloc_4298_, sizeof(void*)*4, v_suppressInsideQuot_4290_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4302_){
_start:
{
lean_object* v___f_4303_; lean_object* v___x_4304_; 
v___f_4303_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4304_ = l_Lean_Parser_adaptCacheableContext(v___f_4303_, v_p_4302_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4312_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4313_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4314_ = l_Lean_addBuiltinDocString(v___x_4312_, v___x_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4318_, lean_object* v_s_4319_){
_start:
{
lean_object* v_pos_4320_; lean_object* v_toInputContext_4321_; uint8_t v___x_4322_; 
v_pos_4320_ = lean_ctor_get(v_s_4319_, 2);
v_toInputContext_4321_ = lean_ctor_get(v_c_4318_, 0);
v___x_4322_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4321_, v_pos_4320_);
if (v___x_4322_ == 0)
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4324_ = l_Lean_Parser_ParserState_mkError(v_s_4319_, v___x_4323_);
return v___x_4324_;
}
else
{
return v_s_4319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4325_, lean_object* v_s_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_Parser_eoiFn(v_c_4325_, v_s_4326_);
lean_dec_ref(v_c_4325_);
return v_res_4327_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4329_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
lean_ctor_set(v___x_4330_, 1, v___x_4328_);
return v___x_4330_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4332_, lean_object* v_v_4333_, lean_object* v_t_4334_){
_start:
{
if (lean_obj_tag(v_t_4334_) == 0)
{
lean_object* v_size_4335_; lean_object* v_k_4336_; lean_object* v_v_4337_; lean_object* v_l_4338_; lean_object* v_r_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4619_; 
v_size_4335_ = lean_ctor_get(v_t_4334_, 0);
v_k_4336_ = lean_ctor_get(v_t_4334_, 1);
v_v_4337_ = lean_ctor_get(v_t_4334_, 2);
v_l_4338_ = lean_ctor_get(v_t_4334_, 3);
v_r_4339_ = lean_ctor_get(v_t_4334_, 4);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_t_4334_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4341_ = v_t_4334_;
v_isShared_4342_ = v_isSharedCheck_4619_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_r_4339_);
lean_inc(v_l_4338_);
lean_inc(v_v_4337_);
lean_inc(v_k_4336_);
lean_inc(v_size_4335_);
lean_dec(v_t_4334_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4619_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
uint8_t v___x_4343_; 
v___x_4343_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4332_, v_k_4336_);
switch(v___x_4343_)
{
case 0:
{
lean_object* v_impl_4344_; lean_object* v___x_4345_; 
lean_dec(v_size_4335_);
v_impl_4344_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4332_, v_v_4333_, v_l_4338_);
v___x_4345_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4339_) == 0)
{
lean_object* v_size_4346_; lean_object* v_size_4347_; lean_object* v_k_4348_; lean_object* v_v_4349_; lean_object* v_l_4350_; lean_object* v_r_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v_size_4346_ = lean_ctor_get(v_r_4339_, 0);
v_size_4347_ = lean_ctor_get(v_impl_4344_, 0);
lean_inc(v_size_4347_);
v_k_4348_ = lean_ctor_get(v_impl_4344_, 1);
lean_inc(v_k_4348_);
v_v_4349_ = lean_ctor_get(v_impl_4344_, 2);
lean_inc(v_v_4349_);
v_l_4350_ = lean_ctor_get(v_impl_4344_, 3);
lean_inc(v_l_4350_);
v_r_4351_ = lean_ctor_get(v_impl_4344_, 4);
lean_inc(v_r_4351_);
v___x_4352_ = lean_unsigned_to_nat(3u);
v___x_4353_ = lean_nat_mul(v___x_4352_, v_size_4346_);
v___x_4354_ = lean_nat_dec_lt(v___x_4353_, v_size_4347_);
lean_dec(v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
lean_dec(v_r_4351_);
lean_dec(v_l_4350_);
lean_dec(v_v_4349_);
lean_dec(v_k_4348_);
v___x_4355_ = lean_nat_add(v___x_4345_, v_size_4347_);
lean_dec(v_size_4347_);
v___x_4356_ = lean_nat_add(v___x_4355_, v_size_4346_);
lean_dec(v___x_4355_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 3, v_impl_4344_);
lean_ctor_set(v___x_4341_, 0, v___x_4356_);
v___x_4358_ = v___x_4341_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4359_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4359_, 3, v_impl_4344_);
lean_ctor_set(v_reuseFailAlloc_4359_, 4, v_r_4339_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
else
{
lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4425_; 
v_isSharedCheck_4425_ = !lean_is_exclusive(v_impl_4344_);
if (v_isSharedCheck_4425_ == 0)
{
lean_object* v_unused_4426_; lean_object* v_unused_4427_; lean_object* v_unused_4428_; lean_object* v_unused_4429_; lean_object* v_unused_4430_; 
v_unused_4426_ = lean_ctor_get(v_impl_4344_, 4);
lean_dec(v_unused_4426_);
v_unused_4427_ = lean_ctor_get(v_impl_4344_, 3);
lean_dec(v_unused_4427_);
v_unused_4428_ = lean_ctor_get(v_impl_4344_, 2);
lean_dec(v_unused_4428_);
v_unused_4429_ = lean_ctor_get(v_impl_4344_, 1);
lean_dec(v_unused_4429_);
v_unused_4430_ = lean_ctor_get(v_impl_4344_, 0);
lean_dec(v_unused_4430_);
v___x_4361_ = v_impl_4344_;
v_isShared_4362_ = v_isSharedCheck_4425_;
goto v_resetjp_4360_;
}
else
{
lean_dec(v_impl_4344_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4425_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_size_4363_; lean_object* v_size_4364_; lean_object* v_k_4365_; lean_object* v_v_4366_; lean_object* v_l_4367_; lean_object* v_r_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v_size_4363_ = lean_ctor_get(v_l_4350_, 0);
v_size_4364_ = lean_ctor_get(v_r_4351_, 0);
v_k_4365_ = lean_ctor_get(v_r_4351_, 1);
v_v_4366_ = lean_ctor_get(v_r_4351_, 2);
v_l_4367_ = lean_ctor_get(v_r_4351_, 3);
v_r_4368_ = lean_ctor_get(v_r_4351_, 4);
v___x_4369_ = lean_unsigned_to_nat(2u);
v___x_4370_ = lean_nat_mul(v___x_4369_, v_size_4363_);
v___x_4371_ = lean_nat_dec_lt(v_size_4364_, v___x_4370_);
lean_dec(v___x_4370_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4400_; 
lean_inc(v_r_4368_);
lean_inc(v_l_4367_);
lean_inc(v_v_4366_);
lean_inc(v_k_4365_);
v_isSharedCheck_4400_ = !lean_is_exclusive(v_r_4351_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; lean_object* v_unused_4402_; lean_object* v_unused_4403_; lean_object* v_unused_4404_; lean_object* v_unused_4405_; 
v_unused_4401_ = lean_ctor_get(v_r_4351_, 4);
lean_dec(v_unused_4401_);
v_unused_4402_ = lean_ctor_get(v_r_4351_, 3);
lean_dec(v_unused_4402_);
v_unused_4403_ = lean_ctor_get(v_r_4351_, 2);
lean_dec(v_unused_4403_);
v_unused_4404_ = lean_ctor_get(v_r_4351_, 1);
lean_dec(v_unused_4404_);
v_unused_4405_ = lean_ctor_get(v_r_4351_, 0);
lean_dec(v_unused_4405_);
v___x_4373_ = v_r_4351_;
v_isShared_4374_ = v_isSharedCheck_4400_;
goto v_resetjp_4372_;
}
else
{
lean_dec(v_r_4351_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4400_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___x_4388_; lean_object* v___y_4390_; 
v___x_4375_ = lean_nat_add(v___x_4345_, v_size_4347_);
lean_dec(v_size_4347_);
v___x_4376_ = lean_nat_add(v___x_4375_, v_size_4346_);
lean_dec(v___x_4375_);
v___x_4388_ = lean_nat_add(v___x_4345_, v_size_4363_);
if (lean_obj_tag(v_l_4367_) == 0)
{
lean_object* v_size_4398_; 
v_size_4398_ = lean_ctor_get(v_l_4367_, 0);
lean_inc(v_size_4398_);
v___y_4390_ = v_size_4398_;
goto v___jp_4389_;
}
else
{
lean_object* v___x_4399_; 
v___x_4399_ = lean_unsigned_to_nat(0u);
v___y_4390_ = v___x_4399_;
goto v___jp_4389_;
}
v___jp_4377_:
{
lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4381_ = lean_nat_add(v___y_4378_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec(v___y_4378_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 4, v_r_4339_);
lean_ctor_set(v___x_4373_, 3, v_r_4368_);
lean_ctor_set(v___x_4373_, 2, v_v_4337_);
lean_ctor_set(v___x_4373_, 1, v_k_4336_);
lean_ctor_set(v___x_4373_, 0, v___x_4381_);
v___x_4383_ = v___x_4373_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4387_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4387_, 3, v_r_4368_);
lean_ctor_set(v_reuseFailAlloc_4387_, 4, v_r_4339_);
v___x_4383_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4385_; 
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 4, v___x_4383_);
lean_ctor_set(v___x_4361_, 3, v___y_4379_);
lean_ctor_set(v___x_4361_, 2, v_v_4366_);
lean_ctor_set(v___x_4361_, 1, v_k_4365_);
lean_ctor_set(v___x_4361_, 0, v___x_4376_);
v___x_4385_ = v___x_4361_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_k_4365_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_v_4366_);
lean_ctor_set(v_reuseFailAlloc_4386_, 3, v___y_4379_);
lean_ctor_set(v_reuseFailAlloc_4386_, 4, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
v___jp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4391_ = lean_nat_add(v___x_4388_, v___y_4390_);
lean_dec(v___y_4390_);
lean_dec(v___x_4388_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v_l_4367_);
lean_ctor_set(v___x_4341_, 3, v_l_4350_);
lean_ctor_set(v___x_4341_, 2, v_v_4349_);
lean_ctor_set(v___x_4341_, 1, v_k_4348_);
lean_ctor_set(v___x_4341_, 0, v___x_4391_);
v___x_4393_ = v___x_4341_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_k_4348_);
lean_ctor_set(v_reuseFailAlloc_4397_, 2, v_v_4349_);
lean_ctor_set(v_reuseFailAlloc_4397_, 3, v_l_4350_);
lean_ctor_set(v_reuseFailAlloc_4397_, 4, v_l_4367_);
v___x_4393_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; 
v___x_4394_ = lean_nat_add(v___x_4345_, v_size_4346_);
if (lean_obj_tag(v_r_4368_) == 0)
{
lean_object* v_size_4395_; 
v_size_4395_ = lean_ctor_get(v_r_4368_, 0);
lean_inc(v_size_4395_);
v___y_4378_ = v___x_4394_;
v___y_4379_ = v___x_4393_;
v___y_4380_ = v_size_4395_;
goto v___jp_4377_;
}
else
{
lean_object* v___x_4396_; 
v___x_4396_ = lean_unsigned_to_nat(0u);
v___y_4378_ = v___x_4394_;
v___y_4379_ = v___x_4393_;
v___y_4380_ = v___x_4396_;
goto v___jp_4377_;
}
}
}
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4411_; 
lean_del_object(v___x_4341_);
v___x_4406_ = lean_nat_add(v___x_4345_, v_size_4347_);
lean_dec(v_size_4347_);
v___x_4407_ = lean_nat_add(v___x_4406_, v_size_4346_);
lean_dec(v___x_4406_);
v___x_4408_ = lean_nat_add(v___x_4345_, v_size_4346_);
v___x_4409_ = lean_nat_add(v___x_4408_, v_size_4364_);
lean_dec(v___x_4408_);
lean_inc_ref(v_r_4339_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 4, v_r_4339_);
lean_ctor_set(v___x_4361_, 3, v_r_4351_);
lean_ctor_set(v___x_4361_, 2, v_v_4337_);
lean_ctor_set(v___x_4361_, 1, v_k_4336_);
lean_ctor_set(v___x_4361_, 0, v___x_4409_);
v___x_4411_ = v___x_4361_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4424_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4424_, 3, v_r_4351_);
lean_ctor_set(v_reuseFailAlloc_4424_, 4, v_r_4339_);
v___x_4411_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_isSharedCheck_4418_ = !lean_is_exclusive(v_r_4339_);
if (v_isSharedCheck_4418_ == 0)
{
lean_object* v_unused_4419_; lean_object* v_unused_4420_; lean_object* v_unused_4421_; lean_object* v_unused_4422_; lean_object* v_unused_4423_; 
v_unused_4419_ = lean_ctor_get(v_r_4339_, 4);
lean_dec(v_unused_4419_);
v_unused_4420_ = lean_ctor_get(v_r_4339_, 3);
lean_dec(v_unused_4420_);
v_unused_4421_ = lean_ctor_get(v_r_4339_, 2);
lean_dec(v_unused_4421_);
v_unused_4422_ = lean_ctor_get(v_r_4339_, 1);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_r_4339_, 0);
lean_dec(v_unused_4423_);
v___x_4413_ = v_r_4339_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_dec(v_r_4339_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 4, v___x_4411_);
lean_ctor_set(v___x_4413_, 3, v_l_4350_);
lean_ctor_set(v___x_4413_, 2, v_v_4349_);
lean_ctor_set(v___x_4413_, 1, v_k_4348_);
lean_ctor_set(v___x_4413_, 0, v___x_4407_);
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_k_4348_);
lean_ctor_set(v_reuseFailAlloc_4417_, 2, v_v_4349_);
lean_ctor_set(v_reuseFailAlloc_4417_, 3, v_l_4350_);
lean_ctor_set(v_reuseFailAlloc_4417_, 4, v___x_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4431_; 
v_l_4431_ = lean_ctor_get(v_impl_4344_, 3);
lean_inc(v_l_4431_);
if (lean_obj_tag(v_l_4431_) == 0)
{
lean_object* v_r_4432_; lean_object* v_k_4433_; lean_object* v_v_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4445_; 
v_r_4432_ = lean_ctor_get(v_impl_4344_, 4);
v_k_4433_ = lean_ctor_get(v_impl_4344_, 1);
v_v_4434_ = lean_ctor_get(v_impl_4344_, 2);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_impl_4344_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; lean_object* v_unused_4447_; 
v_unused_4446_ = lean_ctor_get(v_impl_4344_, 3);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_impl_4344_, 0);
lean_dec(v_unused_4447_);
v___x_4436_ = v_impl_4344_;
v_isShared_4437_ = v_isSharedCheck_4445_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_r_4432_);
lean_inc(v_v_4434_);
lean_inc(v_k_4433_);
lean_dec(v_impl_4344_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4445_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4438_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4432_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 3, v_r_4432_);
lean_ctor_set(v___x_4436_, 2, v_v_4337_);
lean_ctor_set(v___x_4436_, 1, v_k_4336_);
lean_ctor_set(v___x_4436_, 0, v___x_4345_);
v___x_4440_ = v___x_4436_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4444_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4444_, 3, v_r_4432_);
lean_ctor_set(v_reuseFailAlloc_4444_, 4, v_r_4432_);
v___x_4440_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
lean_object* v___x_4442_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v___x_4440_);
lean_ctor_set(v___x_4341_, 3, v_l_4431_);
lean_ctor_set(v___x_4341_, 2, v_v_4434_);
lean_ctor_set(v___x_4341_, 1, v_k_4433_);
lean_ctor_set(v___x_4341_, 0, v___x_4438_);
v___x_4442_ = v___x_4341_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4438_);
lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_k_4433_);
lean_ctor_set(v_reuseFailAlloc_4443_, 2, v_v_4434_);
lean_ctor_set(v_reuseFailAlloc_4443_, 3, v_l_4431_);
lean_ctor_set(v_reuseFailAlloc_4443_, 4, v___x_4440_);
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
else
{
lean_object* v_r_4448_; 
v_r_4448_ = lean_ctor_get(v_impl_4344_, 4);
lean_inc(v_r_4448_);
if (lean_obj_tag(v_r_4448_) == 0)
{
lean_object* v_k_4449_; lean_object* v_v_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4473_; 
v_k_4449_ = lean_ctor_get(v_impl_4344_, 1);
v_v_4450_ = lean_ctor_get(v_impl_4344_, 2);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_impl_4344_);
if (v_isSharedCheck_4473_ == 0)
{
lean_object* v_unused_4474_; lean_object* v_unused_4475_; lean_object* v_unused_4476_; 
v_unused_4474_ = lean_ctor_get(v_impl_4344_, 4);
lean_dec(v_unused_4474_);
v_unused_4475_ = lean_ctor_get(v_impl_4344_, 3);
lean_dec(v_unused_4475_);
v_unused_4476_ = lean_ctor_get(v_impl_4344_, 0);
lean_dec(v_unused_4476_);
v___x_4452_ = v_impl_4344_;
v_isShared_4453_ = v_isSharedCheck_4473_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_v_4450_);
lean_inc(v_k_4449_);
lean_dec(v_impl_4344_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4473_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v_k_4454_; lean_object* v_v_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4469_; 
v_k_4454_ = lean_ctor_get(v_r_4448_, 1);
v_v_4455_ = lean_ctor_get(v_r_4448_, 2);
v_isSharedCheck_4469_ = !lean_is_exclusive(v_r_4448_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; lean_object* v_unused_4471_; lean_object* v_unused_4472_; 
v_unused_4470_ = lean_ctor_get(v_r_4448_, 4);
lean_dec(v_unused_4470_);
v_unused_4471_ = lean_ctor_get(v_r_4448_, 3);
lean_dec(v_unused_4471_);
v_unused_4472_ = lean_ctor_get(v_r_4448_, 0);
lean_dec(v_unused_4472_);
v___x_4457_ = v_r_4448_;
v_isShared_4458_ = v_isSharedCheck_4469_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_v_4455_);
lean_inc(v_k_4454_);
lean_dec(v_r_4448_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4469_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; lean_object* v___x_4461_; 
v___x_4459_ = lean_unsigned_to_nat(3u);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 4, v_l_4431_);
lean_ctor_set(v___x_4457_, 3, v_l_4431_);
lean_ctor_set(v___x_4457_, 2, v_v_4450_);
lean_ctor_set(v___x_4457_, 1, v_k_4449_);
lean_ctor_set(v___x_4457_, 0, v___x_4345_);
v___x_4461_ = v___x_4457_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_k_4449_);
lean_ctor_set(v_reuseFailAlloc_4468_, 2, v_v_4450_);
lean_ctor_set(v_reuseFailAlloc_4468_, 3, v_l_4431_);
lean_ctor_set(v_reuseFailAlloc_4468_, 4, v_l_4431_);
v___x_4461_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4463_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 4, v_l_4431_);
lean_ctor_set(v___x_4452_, 2, v_v_4337_);
lean_ctor_set(v___x_4452_, 1, v_k_4336_);
lean_ctor_set(v___x_4452_, 0, v___x_4345_);
v___x_4463_ = v___x_4452_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4467_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4467_, 3, v_l_4431_);
lean_ctor_set(v_reuseFailAlloc_4467_, 4, v_l_4431_);
v___x_4463_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
lean_object* v___x_4465_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v___x_4463_);
lean_ctor_set(v___x_4341_, 3, v___x_4461_);
lean_ctor_set(v___x_4341_, 2, v_v_4455_);
lean_ctor_set(v___x_4341_, 1, v_k_4454_);
lean_ctor_set(v___x_4341_, 0, v___x_4459_);
v___x_4465_ = v___x_4341_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4459_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v_k_4454_);
lean_ctor_set(v_reuseFailAlloc_4466_, 2, v_v_4455_);
lean_ctor_set(v_reuseFailAlloc_4466_, 3, v___x_4461_);
lean_ctor_set(v_reuseFailAlloc_4466_, 4, v___x_4463_);
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
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = lean_unsigned_to_nat(2u);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v_r_4448_);
lean_ctor_set(v___x_4341_, 3, v_impl_4344_);
lean_ctor_set(v___x_4341_, 0, v___x_4477_);
v___x_4479_ = v___x_4341_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v_impl_4344_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v_r_4448_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4482_; 
lean_dec(v_v_4337_);
lean_dec(v_k_4336_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 2, v_v_4333_);
lean_ctor_set(v___x_4341_, 1, v_k_4332_);
v___x_4482_ = v___x_4341_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_size_4335_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_k_4332_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v_v_4333_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v_l_4338_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v_r_4339_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
default: 
{
lean_object* v_impl_4484_; lean_object* v___x_4485_; 
lean_dec(v_size_4335_);
v_impl_4484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4332_, v_v_4333_, v_r_4339_);
v___x_4485_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4338_) == 0)
{
lean_object* v_size_4486_; lean_object* v_size_4487_; lean_object* v_k_4488_; lean_object* v_v_4489_; lean_object* v_l_4490_; lean_object* v_r_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v_size_4486_ = lean_ctor_get(v_l_4338_, 0);
v_size_4487_ = lean_ctor_get(v_impl_4484_, 0);
lean_inc(v_size_4487_);
v_k_4488_ = lean_ctor_get(v_impl_4484_, 1);
lean_inc(v_k_4488_);
v_v_4489_ = lean_ctor_get(v_impl_4484_, 2);
lean_inc(v_v_4489_);
v_l_4490_ = lean_ctor_get(v_impl_4484_, 3);
lean_inc(v_l_4490_);
v_r_4491_ = lean_ctor_get(v_impl_4484_, 4);
lean_inc(v_r_4491_);
v___x_4492_ = lean_unsigned_to_nat(3u);
v___x_4493_ = lean_nat_mul(v___x_4492_, v_size_4486_);
v___x_4494_ = lean_nat_dec_lt(v___x_4493_, v_size_4487_);
lean_dec(v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4498_; 
lean_dec(v_r_4491_);
lean_dec(v_l_4490_);
lean_dec(v_v_4489_);
lean_dec(v_k_4488_);
v___x_4495_ = lean_nat_add(v___x_4485_, v_size_4486_);
v___x_4496_ = lean_nat_add(v___x_4495_, v_size_4487_);
lean_dec(v_size_4487_);
lean_dec(v___x_4495_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v_impl_4484_);
lean_ctor_set(v___x_4341_, 0, v___x_4496_);
v___x_4498_ = v___x_4341_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v_l_4338_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v_impl_4484_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
else
{
lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4563_; 
v_isSharedCheck_4563_ = !lean_is_exclusive(v_impl_4484_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; lean_object* v_unused_4565_; lean_object* v_unused_4566_; lean_object* v_unused_4567_; lean_object* v_unused_4568_; 
v_unused_4564_ = lean_ctor_get(v_impl_4484_, 4);
lean_dec(v_unused_4564_);
v_unused_4565_ = lean_ctor_get(v_impl_4484_, 3);
lean_dec(v_unused_4565_);
v_unused_4566_ = lean_ctor_get(v_impl_4484_, 2);
lean_dec(v_unused_4566_);
v_unused_4567_ = lean_ctor_get(v_impl_4484_, 1);
lean_dec(v_unused_4567_);
v_unused_4568_ = lean_ctor_get(v_impl_4484_, 0);
lean_dec(v_unused_4568_);
v___x_4501_ = v_impl_4484_;
v_isShared_4502_ = v_isSharedCheck_4563_;
goto v_resetjp_4500_;
}
else
{
lean_dec(v_impl_4484_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4563_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v_size_4503_; lean_object* v_k_4504_; lean_object* v_v_4505_; lean_object* v_l_4506_; lean_object* v_r_4507_; lean_object* v_size_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v_size_4503_ = lean_ctor_get(v_l_4490_, 0);
v_k_4504_ = lean_ctor_get(v_l_4490_, 1);
v_v_4505_ = lean_ctor_get(v_l_4490_, 2);
v_l_4506_ = lean_ctor_get(v_l_4490_, 3);
v_r_4507_ = lean_ctor_get(v_l_4490_, 4);
v_size_4508_ = lean_ctor_get(v_r_4491_, 0);
v___x_4509_ = lean_unsigned_to_nat(2u);
v___x_4510_ = lean_nat_mul(v___x_4509_, v_size_4508_);
v___x_4511_ = lean_nat_dec_lt(v_size_4503_, v___x_4510_);
lean_dec(v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4539_; 
lean_inc(v_r_4507_);
lean_inc(v_l_4506_);
lean_inc(v_v_4505_);
lean_inc(v_k_4504_);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_l_4490_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; lean_object* v_unused_4541_; lean_object* v_unused_4542_; lean_object* v_unused_4543_; lean_object* v_unused_4544_; 
v_unused_4540_ = lean_ctor_get(v_l_4490_, 4);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_l_4490_, 3);
lean_dec(v_unused_4541_);
v_unused_4542_ = lean_ctor_get(v_l_4490_, 2);
lean_dec(v_unused_4542_);
v_unused_4543_ = lean_ctor_get(v_l_4490_, 1);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_l_4490_, 0);
lean_dec(v_unused_4544_);
v___x_4513_ = v_l_4490_;
v_isShared_4514_ = v_isSharedCheck_4539_;
goto v_resetjp_4512_;
}
else
{
lean_dec(v_l_4490_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4539_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4529_; 
v___x_4515_ = lean_nat_add(v___x_4485_, v_size_4486_);
v___x_4516_ = lean_nat_add(v___x_4515_, v_size_4487_);
lean_dec(v_size_4487_);
if (lean_obj_tag(v_l_4506_) == 0)
{
lean_object* v_size_4537_; 
v_size_4537_ = lean_ctor_get(v_l_4506_, 0);
lean_inc(v_size_4537_);
v___y_4529_ = v_size_4537_;
goto v___jp_4528_;
}
else
{
lean_object* v___x_4538_; 
v___x_4538_ = lean_unsigned_to_nat(0u);
v___y_4529_ = v___x_4538_;
goto v___jp_4528_;
}
v___jp_4517_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = lean_nat_add(v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec(v___y_4519_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 4, v_r_4491_);
lean_ctor_set(v___x_4513_, 3, v_r_4507_);
lean_ctor_set(v___x_4513_, 2, v_v_4489_);
lean_ctor_set(v___x_4513_, 1, v_k_4488_);
lean_ctor_set(v___x_4513_, 0, v___x_4521_);
v___x_4523_ = v___x_4513_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_k_4488_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_v_4489_);
lean_ctor_set(v_reuseFailAlloc_4527_, 3, v_r_4507_);
lean_ctor_set(v_reuseFailAlloc_4527_, 4, v_r_4491_);
v___x_4523_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4525_; 
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 4, v___x_4523_);
lean_ctor_set(v___x_4501_, 3, v___y_4518_);
lean_ctor_set(v___x_4501_, 2, v_v_4505_);
lean_ctor_set(v___x_4501_, 1, v_k_4504_);
lean_ctor_set(v___x_4501_, 0, v___x_4516_);
v___x_4525_ = v___x_4501_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4516_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_k_4504_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v_v_4505_);
lean_ctor_set(v_reuseFailAlloc_4526_, 3, v___y_4518_);
lean_ctor_set(v_reuseFailAlloc_4526_, 4, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
v___jp_4528_:
{
lean_object* v___x_4530_; lean_object* v___x_4532_; 
v___x_4530_ = lean_nat_add(v___x_4515_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec(v___x_4515_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v_l_4506_);
lean_ctor_set(v___x_4341_, 0, v___x_4530_);
v___x_4532_ = v___x_4341_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4536_, 3, v_l_4338_);
lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_l_4506_);
v___x_4532_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
lean_object* v___x_4533_; 
v___x_4533_ = lean_nat_add(v___x_4485_, v_size_4508_);
if (lean_obj_tag(v_r_4507_) == 0)
{
lean_object* v_size_4534_; 
v_size_4534_ = lean_ctor_get(v_r_4507_, 0);
lean_inc(v_size_4534_);
v___y_4518_ = v___x_4532_;
v___y_4519_ = v___x_4533_;
v___y_4520_ = v_size_4534_;
goto v___jp_4517_;
}
else
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_unsigned_to_nat(0u);
v___y_4518_ = v___x_4532_;
v___y_4519_ = v___x_4533_;
v___y_4520_ = v___x_4535_;
goto v___jp_4517_;
}
}
}
}
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
lean_del_object(v___x_4341_);
v___x_4545_ = lean_nat_add(v___x_4485_, v_size_4486_);
v___x_4546_ = lean_nat_add(v___x_4545_, v_size_4487_);
lean_dec(v_size_4487_);
v___x_4547_ = lean_nat_add(v___x_4545_, v_size_4503_);
lean_dec(v___x_4545_);
lean_inc_ref(v_l_4338_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 4, v_l_4490_);
lean_ctor_set(v___x_4501_, 3, v_l_4338_);
lean_ctor_set(v___x_4501_, 2, v_v_4337_);
lean_ctor_set(v___x_4501_, 1, v_k_4336_);
lean_ctor_set(v___x_4501_, 0, v___x_4547_);
v___x_4549_ = v___x_4501_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4562_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4562_, 3, v_l_4338_);
lean_ctor_set(v_reuseFailAlloc_4562_, 4, v_l_4490_);
v___x_4549_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
v_isSharedCheck_4556_ = !lean_is_exclusive(v_l_4338_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; lean_object* v_unused_4558_; lean_object* v_unused_4559_; lean_object* v_unused_4560_; lean_object* v_unused_4561_; 
v_unused_4557_ = lean_ctor_get(v_l_4338_, 4);
lean_dec(v_unused_4557_);
v_unused_4558_ = lean_ctor_get(v_l_4338_, 3);
lean_dec(v_unused_4558_);
v_unused_4559_ = lean_ctor_get(v_l_4338_, 2);
lean_dec(v_unused_4559_);
v_unused_4560_ = lean_ctor_get(v_l_4338_, 1);
lean_dec(v_unused_4560_);
v_unused_4561_ = lean_ctor_get(v_l_4338_, 0);
lean_dec(v_unused_4561_);
v___x_4551_ = v_l_4338_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_dec(v_l_4338_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 4, v_r_4491_);
lean_ctor_set(v___x_4551_, 3, v___x_4549_);
lean_ctor_set(v___x_4551_, 2, v_v_4489_);
lean_ctor_set(v___x_4551_, 1, v_k_4488_);
lean_ctor_set(v___x_4551_, 0, v___x_4546_);
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_k_4488_);
lean_ctor_set(v_reuseFailAlloc_4555_, 2, v_v_4489_);
lean_ctor_set(v_reuseFailAlloc_4555_, 3, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4555_, 4, v_r_4491_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4569_; 
v_l_4569_ = lean_ctor_get(v_impl_4484_, 3);
lean_inc(v_l_4569_);
if (lean_obj_tag(v_l_4569_) == 0)
{
lean_object* v_r_4570_; lean_object* v_k_4571_; lean_object* v_v_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4595_; 
v_r_4570_ = lean_ctor_get(v_impl_4484_, 4);
v_k_4571_ = lean_ctor_get(v_impl_4484_, 1);
v_v_4572_ = lean_ctor_get(v_impl_4484_, 2);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_impl_4484_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; lean_object* v_unused_4597_; 
v_unused_4596_ = lean_ctor_get(v_impl_4484_, 3);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_impl_4484_, 0);
lean_dec(v_unused_4597_);
v___x_4574_ = v_impl_4484_;
v_isShared_4575_ = v_isSharedCheck_4595_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_r_4570_);
lean_inc(v_v_4572_);
lean_inc(v_k_4571_);
lean_dec(v_impl_4484_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4595_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v_k_4576_; lean_object* v_v_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4591_; 
v_k_4576_ = lean_ctor_get(v_l_4569_, 1);
v_v_4577_ = lean_ctor_get(v_l_4569_, 2);
v_isSharedCheck_4591_ = !lean_is_exclusive(v_l_4569_);
if (v_isSharedCheck_4591_ == 0)
{
lean_object* v_unused_4592_; lean_object* v_unused_4593_; lean_object* v_unused_4594_; 
v_unused_4592_ = lean_ctor_get(v_l_4569_, 4);
lean_dec(v_unused_4592_);
v_unused_4593_ = lean_ctor_get(v_l_4569_, 3);
lean_dec(v_unused_4593_);
v_unused_4594_ = lean_ctor_get(v_l_4569_, 0);
lean_dec(v_unused_4594_);
v___x_4579_ = v_l_4569_;
v_isShared_4580_ = v_isSharedCheck_4591_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_v_4577_);
lean_inc(v_k_4576_);
lean_dec(v_l_4569_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4591_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4581_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4570_, 2);
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 4, v_r_4570_);
lean_ctor_set(v___x_4579_, 3, v_r_4570_);
lean_ctor_set(v___x_4579_, 2, v_v_4337_);
lean_ctor_set(v___x_4579_, 1, v_k_4336_);
lean_ctor_set(v___x_4579_, 0, v___x_4485_);
v___x_4583_ = v___x_4579_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4590_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4590_, 3, v_r_4570_);
lean_ctor_set(v_reuseFailAlloc_4590_, 4, v_r_4570_);
v___x_4583_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4585_; 
lean_inc(v_r_4570_);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 3, v_r_4570_);
lean_ctor_set(v___x_4574_, 0, v___x_4485_);
v___x_4585_ = v___x_4574_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_k_4571_);
lean_ctor_set(v_reuseFailAlloc_4589_, 2, v_v_4572_);
lean_ctor_set(v_reuseFailAlloc_4589_, 3, v_r_4570_);
lean_ctor_set(v_reuseFailAlloc_4589_, 4, v_r_4570_);
v___x_4585_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4587_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v___x_4585_);
lean_ctor_set(v___x_4341_, 3, v___x_4583_);
lean_ctor_set(v___x_4341_, 2, v_v_4577_);
lean_ctor_set(v___x_4341_, 1, v_k_4576_);
lean_ctor_set(v___x_4341_, 0, v___x_4581_);
v___x_4587_ = v___x_4341_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v_k_4576_);
lean_ctor_set(v_reuseFailAlloc_4588_, 2, v_v_4577_);
lean_ctor_set(v_reuseFailAlloc_4588_, 3, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4588_, 4, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
}
else
{
lean_object* v_r_4598_; 
v_r_4598_ = lean_ctor_get(v_impl_4484_, 4);
lean_inc(v_r_4598_);
if (lean_obj_tag(v_r_4598_) == 0)
{
lean_object* v_k_4599_; lean_object* v_v_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4611_; 
v_k_4599_ = lean_ctor_get(v_impl_4484_, 1);
v_v_4600_ = lean_ctor_get(v_impl_4484_, 2);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_impl_4484_);
if (v_isSharedCheck_4611_ == 0)
{
lean_object* v_unused_4612_; lean_object* v_unused_4613_; lean_object* v_unused_4614_; 
v_unused_4612_ = lean_ctor_get(v_impl_4484_, 4);
lean_dec(v_unused_4612_);
v_unused_4613_ = lean_ctor_get(v_impl_4484_, 3);
lean_dec(v_unused_4613_);
v_unused_4614_ = lean_ctor_get(v_impl_4484_, 0);
lean_dec(v_unused_4614_);
v___x_4602_ = v_impl_4484_;
v_isShared_4603_ = v_isSharedCheck_4611_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_v_4600_);
lean_inc(v_k_4599_);
lean_dec(v_impl_4484_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4611_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4604_ = lean_unsigned_to_nat(3u);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 4, v_l_4569_);
lean_ctor_set(v___x_4602_, 2, v_v_4337_);
lean_ctor_set(v___x_4602_, 1, v_k_4336_);
lean_ctor_set(v___x_4602_, 0, v___x_4485_);
v___x_4606_ = v___x_4602_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4610_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4610_, 3, v_l_4569_);
lean_ctor_set(v_reuseFailAlloc_4610_, 4, v_l_4569_);
v___x_4606_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4608_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v_r_4598_);
lean_ctor_set(v___x_4341_, 3, v___x_4606_);
lean_ctor_set(v___x_4341_, 2, v_v_4600_);
lean_ctor_set(v___x_4341_, 1, v_k_4599_);
lean_ctor_set(v___x_4341_, 0, v___x_4604_);
v___x_4608_ = v___x_4341_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_k_4599_);
lean_ctor_set(v_reuseFailAlloc_4609_, 2, v_v_4600_);
lean_ctor_set(v_reuseFailAlloc_4609_, 3, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4609_, 4, v_r_4598_);
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
else
{
lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4615_ = lean_unsigned_to_nat(2u);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 4, v_impl_4484_);
lean_ctor_set(v___x_4341_, 3, v_r_4598_);
lean_ctor_set(v___x_4341_, 0, v___x_4615_);
v___x_4617_ = v___x_4341_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4618_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4618_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4618_, 3, v_r_4598_);
lean_ctor_set(v_reuseFailAlloc_4618_, 4, v_impl_4484_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
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
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_unsigned_to_nat(1u);
v___x_4621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
lean_ctor_set(v___x_4621_, 1, v_k_4332_);
lean_ctor_set(v___x_4621_, 2, v_v_4333_);
lean_ctor_set(v___x_4621_, 3, v_t_4334_);
lean_ctor_set(v___x_4621_, 4, v_t_4334_);
return v___x_4621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4622_, lean_object* v_k_4623_){
_start:
{
if (lean_obj_tag(v_t_4622_) == 0)
{
lean_object* v_k_4624_; lean_object* v_v_4625_; lean_object* v_l_4626_; lean_object* v_r_4627_; uint8_t v___x_4628_; 
v_k_4624_ = lean_ctor_get(v_t_4622_, 1);
v_v_4625_ = lean_ctor_get(v_t_4622_, 2);
v_l_4626_ = lean_ctor_get(v_t_4622_, 3);
v_r_4627_ = lean_ctor_get(v_t_4622_, 4);
v___x_4628_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4623_, v_k_4624_);
switch(v___x_4628_)
{
case 0:
{
v_t_4622_ = v_l_4626_;
goto _start;
}
case 1:
{
lean_object* v___x_4630_; 
lean_inc(v_v_4625_);
v___x_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4630_, 0, v_v_4625_);
return v___x_4630_;
}
default: 
{
v_t_4622_ = v_r_4627_;
goto _start;
}
}
}
else
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_box(0);
return v___x_4632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4633_, lean_object* v_k_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4633_, v_k_4634_);
lean_dec(v_k_4634_);
lean_dec(v_t_4633_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4636_, lean_object* v_k_4637_, lean_object* v_v_4638_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4636_, v_k_4637_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = lean_box(0);
v___x_4641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4641_, 0, v_v_4638_);
lean_ctor_set(v___x_4641_, 1, v___x_4640_);
v___x_4642_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4637_, v___x_4641_, v_map_4636_);
return v___x_4642_;
}
else
{
lean_object* v_val_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v_val_4643_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_val_4643_);
lean_dec_ref_known(v___x_4639_, 1);
v___x_4644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4644_, 0, v_v_4638_);
lean_ctor_set(v___x_4644_, 1, v_val_4643_);
v___x_4645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4637_, v___x_4644_, v_map_4636_);
return v___x_4645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4646_, lean_object* v_map_4647_, lean_object* v_k_4648_, lean_object* v_v_4649_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4647_, v_k_4648_, v_v_4649_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4651_, lean_object* v_t_4652_, lean_object* v_k_4653_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4652_, v_k_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4655_, lean_object* v_t_4656_, lean_object* v_k_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4655_, v_t_4656_, v_k_4657_);
lean_dec(v_k_4657_);
lean_dec(v_t_4656_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4659_, lean_object* v_k_4660_, lean_object* v_v_4661_, lean_object* v_t_4662_, lean_object* v_hl_4663_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4660_, v_v_4661_, v_t_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4665_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_box(1);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4667_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = lean_box(1);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4669_, lean_object* v_a_4670_, lean_object* v_b_4671_, lean_object* v_c_4672_){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4673_, 0, v_a_4670_);
lean_ctor_set(v___x_4673_, 1, v_b_4671_);
v___x_4674_ = lean_apply_2(v_f_4669_, v___x_4673_, v_c_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4675_, lean_object* v_____do__lift_4676_){
_start:
{
lean_object* v_a_4677_; lean_object* v___x_4678_; 
v_a_4677_ = lean_ctor_get(v_____do__lift_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref(v_____do__lift_4676_);
v___x_4678_ = lean_apply_2(v_toPure_4675_, lean_box(0), v_a_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4679_, lean_object* v_m_4680_, lean_object* v_init_4681_, lean_object* v_f_4682_){
_start:
{
lean_object* v_toApplicative_4683_; lean_object* v_toBind_4684_; lean_object* v_toPure_4685_; lean_object* v___f_4686_; lean_object* v___x_4687_; lean_object* v___f_4688_; lean_object* v___x_4689_; 
v_toApplicative_4683_ = lean_ctor_get(v_inst_4679_, 0);
v_toBind_4684_ = lean_ctor_get(v_inst_4679_, 1);
lean_inc(v_toBind_4684_);
v_toPure_4685_ = lean_ctor_get(v_toApplicative_4683_, 1);
lean_inc(v_toPure_4685_);
v___f_4686_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4686_, 0, v_f_4682_);
v___x_4687_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4679_, v___f_4686_, v_init_4681_, v_m_4680_);
v___f_4688_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4688_, 0, v_toPure_4685_);
v___x_4689_ = lean_apply_4(v_toBind_4684_, lean_box(0), lean_box(0), v___x_4687_, v___f_4688_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4690_, lean_object* v_00_u03b1_4691_, lean_object* v_inst_4692_, lean_object* v_00_u03b2_4693_, lean_object* v_m_4694_, lean_object* v_init_4695_, lean_object* v_f_4696_){
_start:
{
lean_object* v_toApplicative_4697_; lean_object* v_toBind_4698_; lean_object* v_toPure_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; lean_object* v___f_4702_; lean_object* v___x_4703_; 
v_toApplicative_4697_ = lean_ctor_get(v_inst_4692_, 0);
v_toBind_4698_ = lean_ctor_get(v_inst_4692_, 1);
lean_inc(v_toBind_4698_);
v_toPure_4699_ = lean_ctor_get(v_toApplicative_4697_, 1);
lean_inc(v_toPure_4699_);
v___f_4700_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4700_, 0, v_f_4696_);
v___x_4701_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4692_, v___f_4700_, v_init_4695_, v_m_4694_);
v___f_4702_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4702_, 0, v_toPure_4699_);
v___x_4703_ = lean_apply_4(v_toBind_4698_, lean_box(0), lean_box(0), v___x_4701_, v___f_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4704_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4705_, 0, lean_box(0));
lean_closure_set(v___x_4705_, 1, lean_box(0));
lean_closure_set(v___x_4705_, 2, v_inst_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4706_, lean_object* v_00_u03b1_4707_, lean_object* v_inst_4708_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4709_, 0, lean_box(0));
lean_closure_set(v___x_4709_, 1, lean_box(0));
lean_closure_set(v___x_4709_, 2, v_inst_4708_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t v_x_4714_){
_start:
{
switch(v_x_4714_)
{
case 0:
{
lean_object* v___x_4715_; 
v___x_4715_ = lean_unsigned_to_nat(0u);
return v___x_4715_;
}
case 1:
{
lean_object* v___x_4716_; 
v___x_4716_ = lean_unsigned_to_nat(1u);
return v___x_4716_;
}
default: 
{
lean_object* v___x_4717_; 
v___x_4717_ = lean_unsigned_to_nat(2u);
return v___x_4717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object* v_x_4718_){
_start:
{
uint8_t v_x_boxed_4719_; lean_object* v_res_4720_; 
v_x_boxed_4719_ = lean_unbox(v_x_4718_);
v_res_4720_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_boxed_4719_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t v_x_4721_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object* v_x_4723_){
_start:
{
uint8_t v_x_4__boxed_4724_; lean_object* v_res_4725_; 
v_x_4__boxed_4724_ = lean_unbox(v_x_4723_);
v_res_4725_ = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(v_x_4__boxed_4724_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4726_){
_start:
{
lean_inc(v_k_4726_);
return v_k_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4727_);
lean_dec(v_k_4727_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4729_, lean_object* v_ctorIdx_4730_, uint8_t v_t_4731_, lean_object* v_h_4732_, lean_object* v_k_4733_){
_start:
{
lean_inc(v_k_4733_);
return v_k_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4734_, lean_object* v_ctorIdx_4735_, lean_object* v_t_4736_, lean_object* v_h_4737_, lean_object* v_k_4738_){
_start:
{
uint8_t v_t_boxed_4739_; lean_object* v_res_4740_; 
v_t_boxed_4739_ = lean_unbox(v_t_4736_);
v_res_4740_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4734_, v_ctorIdx_4735_, v_t_boxed_4739_, v_h_4737_, v_k_4738_);
lean_dec(v_k_4738_);
lean_dec(v_ctorIdx_4735_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4741_){
_start:
{
lean_inc(v_default_4741_);
return v_default_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4742_);
lean_dec(v_default_4742_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4744_, uint8_t v_t_4745_, lean_object* v_h_4746_, lean_object* v_default_4747_){
_start:
{
lean_inc(v_default_4747_);
return v_default_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4748_, lean_object* v_t_4749_, lean_object* v_h_4750_, lean_object* v_default_4751_){
_start:
{
uint8_t v_t_boxed_4752_; lean_object* v_res_4753_; 
v_t_boxed_4752_ = lean_unbox(v_t_4749_);
v_res_4753_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4748_, v_t_boxed_4752_, v_h_4750_, v_default_4751_);
lean_dec(v_default_4751_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4754_){
_start:
{
lean_inc(v_symbol_4754_);
return v_symbol_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4755_);
lean_dec(v_symbol_4755_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4757_, uint8_t v_t_4758_, lean_object* v_h_4759_, lean_object* v_symbol_4760_){
_start:
{
lean_inc(v_symbol_4760_);
return v_symbol_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4761_, lean_object* v_t_4762_, lean_object* v_h_4763_, lean_object* v_symbol_4764_){
_start:
{
uint8_t v_t_boxed_4765_; lean_object* v_res_4766_; 
v_t_boxed_4765_ = lean_unbox(v_t_4762_);
v_res_4766_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4761_, v_t_boxed_4765_, v_h_4763_, v_symbol_4764_);
lean_dec(v_symbol_4764_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4767_){
_start:
{
lean_inc(v_both_4767_);
return v_both_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4768_);
lean_dec(v_both_4768_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4770_, uint8_t v_t_4771_, lean_object* v_h_4772_, lean_object* v_both_4773_){
_start:
{
lean_inc(v_both_4773_);
return v_both_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4774_, lean_object* v_t_4775_, lean_object* v_h_4776_, lean_object* v_both_4777_){
_start:
{
uint8_t v_t_boxed_4778_; lean_object* v_res_4779_; 
v_t_boxed_4778_ = lean_unbox(v_t_4775_);
v_res_4779_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4774_, v_t_boxed_4778_, v_h_4776_, v_both_4777_);
lean_dec(v_both_4777_);
return v_res_4779_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4780_; 
v___x_4780_ = 0;
return v___x_4780_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4781_; 
v___x_4781_ = 0;
return v___x_4781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4782_, uint8_t v_y_4783_){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4784_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4782_);
v___x_4785_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_y_4783_);
v___x_4786_ = lean_nat_dec_eq(v___x_4784_, v___x_4785_);
lean_dec(v___x_4785_);
lean_dec(v___x_4784_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4787_, lean_object* v_y_4788_){
_start:
{
uint8_t v_x_17__boxed_4789_; uint8_t v_y_18__boxed_4790_; uint8_t v_res_4791_; lean_object* v_r_4792_; 
v_x_17__boxed_4789_ = lean_unbox(v_x_4787_);
v_y_18__boxed_4790_ = lean_unbox(v_y_4788_);
v_res_4791_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_17__boxed_4789_, v_y_18__boxed_4790_);
v_r_4792_ = lean_box(v_res_4791_);
return v_r_4792_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_unsigned_to_nat(2u);
v___x_4805_ = lean_nat_to_int(v___x_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4806_, lean_object* v_prec_4807_){
_start:
{
lean_object* v___y_4809_; lean_object* v___y_4816_; lean_object* v___y_4823_; 
switch(v_x_4806_)
{
case 0:
{
lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4829_ = lean_unsigned_to_nat(1024u);
v___x_4830_ = lean_nat_dec_le(v___x_4829_, v_prec_4807_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4809_ = v___x_4831_;
goto v___jp_4808_;
}
else
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4809_ = v___x_4832_;
goto v___jp_4808_;
}
}
case 1:
{
lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4833_ = lean_unsigned_to_nat(1024u);
v___x_4834_ = lean_nat_dec_le(v___x_4833_, v_prec_4807_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; 
v___x_4835_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4816_ = v___x_4835_;
goto v___jp_4815_;
}
else
{
lean_object* v___x_4836_; 
v___x_4836_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4816_ = v___x_4836_;
goto v___jp_4815_;
}
}
default: 
{
lean_object* v___x_4837_; uint8_t v___x_4838_; 
v___x_4837_ = lean_unsigned_to_nat(1024u);
v___x_4838_ = lean_nat_dec_le(v___x_4837_, v_prec_4807_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4823_ = v___x_4839_;
goto v___jp_4822_;
}
else
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4823_ = v___x_4840_;
goto v___jp_4822_;
}
}
}
v___jp_4808_:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4810_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_4809_);
v___x_4811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4811_, 0, v___y_4809_);
lean_ctor_set(v___x_4811_, 1, v___x_4810_);
v___x_4812_ = 0;
v___x_4813_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4813_, 0, v___x_4811_);
lean_ctor_set_uint8(v___x_4813_, sizeof(void*)*1, v___x_4812_);
v___x_4814_ = l_Repr_addAppParen(v___x_4813_, v_prec_4807_);
return v___x_4814_;
}
v___jp_4815_:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4817_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_4816_);
v___x_4818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___y_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = 0;
v___x_4820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set_uint8(v___x_4820_, sizeof(void*)*1, v___x_4819_);
v___x_4821_ = l_Repr_addAppParen(v___x_4820_, v_prec_4807_);
return v___x_4821_;
}
v___jp_4822_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4824_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_4823_);
v___x_4825_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___y_4823_);
lean_ctor_set(v___x_4825_, 1, v___x_4824_);
v___x_4826_ = 0;
v___x_4827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4827_, 0, v___x_4825_);
lean_ctor_set_uint8(v___x_4827_, sizeof(void*)*1, v___x_4826_);
v___x_4828_ = l_Repr_addAppParen(v___x_4827_, v_prec_4807_);
return v___x_4828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_4841_, lean_object* v_prec_4842_){
_start:
{
uint8_t v_x_175__boxed_4843_; lean_object* v_res_4844_; 
v_x_175__boxed_4843_ = lean_unbox(v_x_4841_);
v_res_4844_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_175__boxed_4843_, v_prec_4842_);
lean_dec(v_prec_4842_);
return v_res_4844_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4847_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4850_ = 0;
v___x_4851_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_4852_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_4853_ = lean_box(0);
v___x_4854_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
lean_ctor_set(v___x_4854_, 1, v___x_4852_);
lean_ctor_set(v___x_4854_, 2, v___x_4851_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*3, v___x_4850_);
return v___x_4854_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_4855_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_4857_, lean_object* v_c_4858_, lean_object* v_s_4859_, uint8_t v_behavior_4860_){
_start:
{
lean_object* v___x_4861_; lean_object* v_fst_4862_; lean_object* v_snd_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4905_; 
v___x_4861_ = l_Lean_Parser_peekToken(v_c_4858_, v_s_4859_);
v_fst_4862_ = lean_ctor_get(v___x_4861_, 0);
v_snd_4863_ = lean_ctor_get(v___x_4861_, 1);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4865_ = v___x_4861_;
v_isShared_4866_ = v_isSharedCheck_4905_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_snd_4863_);
lean_inc(v_fst_4862_);
lean_dec(v___x_4861_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4905_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v_n_4868_; 
if (lean_obj_tag(v_snd_4863_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_del_object(v___x_4865_);
lean_dec(v_fst_4862_);
v_a_4880_ = lean_ctor_get(v_snd_4863_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v_snd_4863_, 1);
v___x_4881_ = lean_box(0);
v___x_4882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4882_, 0, v_a_4880_);
lean_ctor_set(v___x_4882_, 1, v___x_4881_);
return v___x_4882_;
}
else
{
lean_object* v_a_4883_; 
v_a_4883_ = lean_ctor_get(v_snd_4863_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v_snd_4863_, 1);
switch(lean_obj_tag(v_a_4883_))
{
case 2:
{
lean_object* v_val_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v_val_4884_ = lean_ctor_get(v_a_4883_, 1);
lean_inc_ref(v_val_4884_);
lean_dec_ref_known(v_a_4883_, 2);
v___x_4885_ = lean_box(0);
v___x_4886_ = l_Lean_Name_str___override(v___x_4885_, v_val_4884_);
v_n_4868_ = v___x_4886_;
goto v___jp_4867_;
}
case 3:
{
switch(v_behavior_4860_)
{
case 0:
{
lean_dec_ref_known(v_a_4883_, 4);
goto v___jp_4878_;
}
case 1:
{
lean_object* v_val_4887_; lean_object* v___x_4888_; 
v_val_4887_ = lean_ctor_get(v_a_4883_, 2);
lean_inc(v_val_4887_);
lean_dec_ref_known(v_a_4883_, 4);
v___x_4888_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4857_, v_val_4887_);
lean_dec(v_val_4887_);
if (lean_obj_tag(v___x_4888_) == 0)
{
goto v___jp_4878_;
}
else
{
lean_object* v_val_4889_; lean_object* v___x_4890_; 
lean_del_object(v___x_4865_);
v_val_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_val_4889_);
lean_dec_ref_known(v___x_4888_, 1);
v___x_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4890_, 0, v_fst_4862_);
lean_ctor_set(v___x_4890_, 1, v_val_4889_);
return v___x_4890_;
}
}
default: 
{
lean_object* v_val_4891_; lean_object* v___x_4892_; 
v_val_4891_ = lean_ctor_get(v_a_4883_, 2);
lean_inc(v_val_4891_);
lean_dec_ref_known(v_a_4883_, 4);
v___x_4892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4857_, v_val_4891_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_dec(v_val_4891_);
goto v___jp_4878_;
}
else
{
lean_object* v_val_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
lean_del_object(v___x_4865_);
v_val_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_val_4893_);
lean_dec_ref_known(v___x_4892_, 1);
v___x_4894_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_4895_ = lean_name_eq(v_val_4891_, v___x_4894_);
lean_dec(v_val_4891_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4857_, v___x_4894_);
if (lean_obj_tag(v___x_4896_) == 1)
{
lean_object* v_val_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
v_val_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_val_4897_);
lean_dec_ref_known(v___x_4896_, 1);
v___x_4898_ = l_List_appendTR___redArg(v_val_4893_, v_val_4897_);
v___x_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4899_, 0, v_fst_4862_);
lean_ctor_set(v___x_4899_, 1, v___x_4898_);
return v___x_4899_;
}
else
{
lean_object* v___x_4900_; 
lean_dec(v___x_4896_);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v_fst_4862_);
lean_ctor_set(v___x_4900_, 1, v_val_4893_);
return v___x_4900_;
}
}
else
{
lean_object* v___x_4901_; 
v___x_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4901_, 0, v_fst_4862_);
lean_ctor_set(v___x_4901_, 1, v_val_4893_);
return v___x_4901_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_4902_; 
v_kind_4902_ = lean_ctor_get(v_a_4883_, 1);
lean_inc(v_kind_4902_);
lean_dec_ref_known(v_a_4883_, 3);
v_n_4868_ = v_kind_4902_;
goto v___jp_4867_;
}
default: 
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
lean_dec(v_a_4883_);
lean_del_object(v___x_4865_);
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_fst_4862_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
return v___x_4904_;
}
}
}
v___jp_4867_:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4857_, v_n_4868_);
lean_dec(v_n_4868_);
if (lean_obj_tag(v___x_4869_) == 1)
{
lean_object* v_val_4870_; lean_object* v___x_4872_; 
v_val_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_val_4870_);
lean_dec_ref_known(v___x_4869_, 1);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 1, v_val_4870_);
v___x_4872_ = v___x_4865_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_fst_4862_);
lean_ctor_set(v_reuseFailAlloc_4873_, 1, v_val_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
lean_dec(v___x_4869_);
v___x_4874_ = lean_box(0);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 1, v___x_4874_);
v___x_4876_ = v___x_4865_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_fst_4862_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
v___jp_4878_:
{
lean_object* v___x_4879_; 
v___x_4879_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_4868_ = v___x_4879_;
goto v___jp_4867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_4906_, lean_object* v_c_4907_, lean_object* v_s_4908_, lean_object* v_behavior_4909_){
_start:
{
uint8_t v_behavior_boxed_4910_; lean_object* v_res_4911_; 
v_behavior_boxed_4910_ = lean_unbox(v_behavior_4909_);
v_res_4911_ = l_Lean_Parser_indexed___redArg(v_map_4906_, v_c_4907_, v_s_4908_, v_behavior_boxed_4910_);
lean_dec(v_map_4906_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_4912_, lean_object* v_map_4913_, lean_object* v_c_4914_, lean_object* v_s_4915_, uint8_t v_behavior_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Parser_indexed___redArg(v_map_4913_, v_c_4914_, v_s_4915_, v_behavior_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_4918_, lean_object* v_map_4919_, lean_object* v_c_4920_, lean_object* v_s_4921_, lean_object* v_behavior_4922_){
_start:
{
uint8_t v_behavior_boxed_4923_; lean_object* v_res_4924_; 
v_behavior_boxed_4923_ = lean_unbox(v_behavior_4922_);
v_res_4924_ = l_Lean_Parser_indexed(v_00_u03b1_4918_, v_map_4919_, v_c_4920_, v_s_4921_, v_behavior_boxed_4923_);
lean_dec(v_map_4919_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Parser_whitespace(v___y_4926_, v___y_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_4929_, v___y_4930_, v___y_4931_);
lean_dec(v_x_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___f_4935_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_4936_ = lean_st_mk_ref(v___f_4935_);
v___x_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_4940_){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4942_ = lean_st_ref_get(v___x_4940_);
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_4944_);
lean_dec(v___x_4944_);
return v_res_4946_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4947_; lean_object* v___f_4948_; 
v___x_4947_ = l_Lean_Parser_categoryParserFnRef;
v___f_4948_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4948_, 0, v___x_4947_);
return v___f_4948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___f_4950_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_4951_ = lean_box(0);
v___x_4952_ = lean_box(2);
v___x_4953_ = l_Lean_registerEnvExtension___redArg(v___f_4950_, v___x_4951_, v___x_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_4957_, v___y_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_4960_, v___y_4961_, v___y_4962_);
lean_dec_ref(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v_a_4960_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_4967_, lean_object* v_ctx_4968_, lean_object* v_s_4969_){
_start:
{
lean_object* v_toParserModuleContext_4970_; lean_object* v_env_4971_; lean_object* v___x_4972_; lean_object* v_asyncMode_4973_; lean_object* v___f_4974_; lean_object* v___x_4975_; lean_object* v___x_11__overap_4976_; lean_object* v___x_4977_; 
v_toParserModuleContext_4970_ = lean_ctor_get(v_ctx_4968_, 1);
v_env_4971_ = lean_ctor_get(v_toParserModuleContext_4970_, 0);
v___x_4972_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_4973_ = lean_ctor_get(v___x_4972_, 2);
v___f_4974_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_4975_ = lean_box(0);
lean_inc_ref(v_env_4971_);
v___x_11__overap_4976_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_4974_, v___x_4972_, v_env_4971_, v_asyncMode_4973_, v___x_4975_);
v___x_4977_ = lean_apply_3(v___x_11__overap_4976_, v_catName_4967_, v_ctx_4968_, v_s_4969_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_4978_, lean_object* v_x_4979_){
_start:
{
lean_object* v_quotDepth_4980_; uint8_t v_suppressInsideQuot_4981_; lean_object* v_savedPos_x3f_4982_; lean_object* v_forbiddenTks_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4990_; 
v_quotDepth_4980_ = lean_ctor_get(v_x_4979_, 1);
v_suppressInsideQuot_4981_ = lean_ctor_get_uint8(v_x_4979_, sizeof(void*)*4);
v_savedPos_x3f_4982_ = lean_ctor_get(v_x_4979_, 2);
v_forbiddenTks_4983_ = lean_ctor_get(v_x_4979_, 3);
v_isSharedCheck_4990_ = !lean_is_exclusive(v_x_4979_);
if (v_isSharedCheck_4990_ == 0)
{
lean_object* v_unused_4991_; 
v_unused_4991_ = lean_ctor_get(v_x_4979_, 0);
lean_dec(v_unused_4991_);
v___x_4985_ = v_x_4979_;
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_forbiddenTks_4983_);
lean_inc(v_savedPos_x3f_4982_);
lean_inc(v_quotDepth_4980_);
lean_dec(v_x_4979_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4988_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v_prec_4978_);
v___x_4988_ = v___x_4985_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_prec_4978_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_quotDepth_4980_);
lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_savedPos_x3f_4982_);
lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_forbiddenTks_4983_);
lean_ctor_set_uint8(v_reuseFailAlloc_4989_, sizeof(void*)*4, v_suppressInsideQuot_4981_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_4992_, lean_object* v_prec_4993_){
_start:
{
lean_object* v___f_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___f_4994_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_4994_, 0, v_prec_4993_);
v___x_4995_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_4992_);
v___x_4996_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_4996_, 0, v_catName_4992_);
v___x_4997_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_4997_, 0, v_catName_4992_);
lean_closure_set(v___x_4997_, 1, v___x_4996_);
v___x_4998_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_4998_, 0, v___f_4994_);
lean_closure_set(v___x_4998_, 1, v___x_4997_);
v___x_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4995_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5003_){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5005_ = l_Lean_Parser_categoryParser(v___x_5004_, v_prec_5003_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5007_, lean_object* v_s_5008_){
_start:
{
lean_object* v_stxStack_5009_; lean_object* v_pos_5010_; lean_object* v_prev_5011_; uint8_t v___x_5012_; 
v_stxStack_5009_ = lean_ctor_get(v_s_5008_, 0);
v_pos_5010_ = lean_ctor_get(v_s_5008_, 2);
v_prev_5011_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5009_);
v___x_5012_ = l_Lean_Parser_checkTailNoWs(v_prev_5011_);
lean_dec(v_prev_5011_);
if (v___x_5012_ == 0)
{
return v_s_5008_;
}
else
{
lean_object* v_toInputContext_5013_; uint8_t v___x_5014_; 
v_toInputContext_5013_ = lean_ctor_get(v_c_5007_, 0);
v___x_5014_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5013_, v_pos_5010_);
if (v___x_5014_ == 0)
{
lean_object* v_inputString_5015_; uint32_t v_curr_5016_; uint32_t v___x_5017_; uint8_t v___x_5018_; 
v_inputString_5015_ = lean_ctor_get(v_toInputContext_5013_, 0);
v_curr_5016_ = lean_string_utf8_get_fast(v_inputString_5015_, v_pos_5010_);
v___x_5017_ = 58;
v___x_5018_ = lean_uint32_dec_eq(v_curr_5016_, v___x_5017_);
if (v___x_5018_ == 0)
{
return v_s_5008_;
}
else
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5019_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5020_ = lean_box(0);
v___x_5021_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5008_, v___x_5019_, v___x_5020_, v___x_5018_);
return v___x_5021_;
}
}
else
{
return v_s_5008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5022_, lean_object* v_s_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5022_, v_s_5023_);
lean_dec_ref(v_c_5022_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5037_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5038_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5039_ = l_Lean_addBuiltinDocString(v___x_5037_, v___x_5038_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5042_, lean_object* v_p_5043_, lean_object* v_c_5044_, lean_object* v_s_5045_){
_start:
{
lean_object* v___x_5046_; lean_object* v_errorMsg_5047_; 
v___x_5046_ = lean_apply_2(v_p_5043_, v_c_5044_, v_s_5045_);
v_errorMsg_5047_ = lean_ctor_get(v___x_5046_, 4);
lean_inc(v_errorMsg_5047_);
if (lean_obj_tag(v_errorMsg_5047_) == 1)
{
lean_object* v_val_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5078_; 
v_val_5048_ = lean_ctor_get(v_errorMsg_5047_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v_errorMsg_5047_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5050_ = v_errorMsg_5047_;
v_isShared_5051_ = v_isSharedCheck_5078_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_val_5048_);
lean_dec(v_errorMsg_5047_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5078_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v_stxStack_5052_; lean_object* v_lhsPrec_5053_; lean_object* v_pos_5054_; lean_object* v_cache_5055_; lean_object* v_recoveredErrors_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5076_; 
v_stxStack_5052_ = lean_ctor_get(v___x_5046_, 0);
v_lhsPrec_5053_ = lean_ctor_get(v___x_5046_, 1);
v_pos_5054_ = lean_ctor_get(v___x_5046_, 2);
v_cache_5055_ = lean_ctor_get(v___x_5046_, 3);
v_recoveredErrors_5056_ = lean_ctor_get(v___x_5046_, 5);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5076_ == 0)
{
lean_object* v_unused_5077_; 
v_unused_5077_ = lean_ctor_get(v___x_5046_, 4);
lean_dec(v_unused_5077_);
v___x_5058_ = v___x_5046_;
v_isShared_5059_ = v_isSharedCheck_5076_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_recoveredErrors_5056_);
lean_inc(v_cache_5055_);
lean_inc(v_pos_5054_);
lean_inc(v_lhsPrec_5053_);
lean_inc(v_stxStack_5052_);
lean_dec(v___x_5046_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5076_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v_unexpectedTk_5060_; lean_object* v_unexpected_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5074_; 
v_unexpectedTk_5060_ = lean_ctor_get(v_val_5048_, 0);
v_unexpected_5061_ = lean_ctor_get(v_val_5048_, 1);
v_isSharedCheck_5074_ = !lean_is_exclusive(v_val_5048_);
if (v_isSharedCheck_5074_ == 0)
{
lean_object* v_unused_5075_; 
v_unused_5075_ = lean_ctor_get(v_val_5048_, 2);
lean_dec(v_unused_5075_);
v___x_5063_ = v_val_5048_;
v_isShared_5064_ = v_isSharedCheck_5074_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_unexpected_5061_);
lean_inc(v_unexpectedTk_5060_);
lean_dec(v_val_5048_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5074_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 2, v_expected_5042_);
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_unexpectedTk_5060_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v_unexpected_5061_);
lean_ctor_set(v_reuseFailAlloc_5073_, 2, v_expected_5042_);
v___x_5066_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5068_; 
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v___x_5066_);
v___x_5068_ = v___x_5050_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5066_);
v___x_5068_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
lean_object* v___x_5070_; 
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 4, v___x_5068_);
v___x_5070_ = v___x_5058_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_stxStack_5052_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_lhsPrec_5053_);
lean_ctor_set(v_reuseFailAlloc_5071_, 2, v_pos_5054_);
lean_ctor_set(v_reuseFailAlloc_5071_, 3, v_cache_5055_);
lean_ctor_set(v_reuseFailAlloc_5071_, 4, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5071_, 5, v_recoveredErrors_5056_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5047_);
lean_dec(v_expected_5042_);
return v___x_5046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5079_, lean_object* v_p_5080_){
_start:
{
lean_object* v_info_5081_; lean_object* v_fn_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5090_; 
v_info_5081_ = lean_ctor_get(v_p_5080_, 0);
v_fn_5082_ = lean_ctor_get(v_p_5080_, 1);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_p_5080_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5084_ = v_p_5080_;
v_isShared_5085_ = v_isSharedCheck_5090_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_fn_5082_);
lean_inc(v_info_5081_);
lean_dec(v_p_5080_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5090_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5086_; lean_object* v___x_5088_; 
v___x_5086_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5086_, 0, v_expected_5079_);
lean_closure_set(v___x_5086_, 1, v_fn_5082_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 1, v___x_5086_);
v___x_5088_ = v___x_5084_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_info_5081_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5097_, lean_object* v_s_5098_){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = ((lean_object*)(l_Lean_Parser_pushNone___lam__0___closed__1));
v___x_5100_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5098_, v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5101_, lean_object* v_s_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l_Lean_Parser_pushNone___lam__0(v_x_5101_, v_s_5102_);
lean_dec_ref(v_x_5101_);
return v_res_5103_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5114_ = l_Lean_Parser_symbolNoAntiquot(v___x_5113_);
return v___x_5114_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = lean_unsigned_to_nat(0u);
v___x_5116_ = l_Lean_Parser_termParser(v___x_5115_);
return v___x_5116_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___x_5117_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5118_ = l_Lean_Parser_decQuotDepth(v___x_5117_);
return v___x_5118_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5119_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5120_ = l_Lean_Parser_symbolNoAntiquot(v___x_5119_);
return v___x_5120_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5121_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5122_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5123_ = l_Lean_Parser_andthen(v___x_5122_, v___x_5121_);
return v___x_5123_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5124_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5125_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5126_ = l_Lean_Parser_andthen(v___x_5125_, v___x_5124_);
return v___x_5126_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5127_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5128_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5129_ = l_Lean_Parser_node(v___x_5128_, v___x_5127_);
return v___x_5129_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5130_; 
v___x_5130_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5130_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5133_ = l_Lean_Parser_symbolNoAntiquot(v___x_5132_);
return v___x_5133_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5134_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5135_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5136_ = l_Lean_Parser_orelse(v___x_5135_, v___x_5134_);
return v___x_5136_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5137_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5138_ = l_Lean_Parser_identNoAntiquot;
v___x_5139_ = l_Lean_Parser_orelse(v___x_5138_, v___x_5137_);
return v___x_5139_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5140_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5142_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5143_ = l_Lean_Parser_checkNoWsBefore(v___x_5142_);
return v___x_5143_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5145_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5146_ = l_Lean_Parser_symbolNoAntiquot(v___x_5145_);
return v___x_5146_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5149_ = l_Lean_Parser_symbolNoAntiquot(v___x_5148_);
return v___x_5149_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5150_ = l_Lean_Parser_antiquotExpr;
v___x_5151_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5152_ = l_Lean_Parser_andthen(v___x_5151_, v___x_5150_);
return v___x_5152_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5153_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5154_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5155_ = l_Lean_Parser_andthen(v___x_5154_, v___x_5153_);
return v___x_5155_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; 
v___x_5156_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5157_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5158_ = l_Lean_Parser_andthen(v___x_5157_, v___x_5156_);
return v___x_5158_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
v___x_5159_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5160_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5161_ = l_Lean_Parser_andthen(v___x_5160_, v___x_5159_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5165_, lean_object* v_s_5166_){
_start:
{
lean_object* v_pos_5167_; lean_object* v_errorMsg_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
v_pos_5167_ = lean_ctor_get(v_s_5166_, 2);
v_errorMsg_5168_ = lean_ctor_get(v_s_5166_, 4);
v___x_5169_ = lean_box(0);
v___x_5170_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5168_, v___x_5169_);
if (v___x_5170_ == 0)
{
lean_dec_ref(v_c_5165_);
return v_s_5166_;
}
else
{
lean_object* v___x_5171_; lean_object* v_fn_5172_; lean_object* v_iniSz_5173_; lean_object* v_s_5174_; lean_object* v_errorMsg_5175_; uint8_t v___x_5176_; 
lean_inc(v_pos_5167_);
v___x_5171_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5172_ = lean_ctor_get(v___x_5171_, 1);
v_iniSz_5173_ = l_Lean_Parser_ParserState_stackSize(v_s_5166_);
lean_inc_ref(v_fn_5172_);
v_s_5174_ = lean_apply_2(v_fn_5172_, v_c_5165_, v_s_5166_);
v_errorMsg_5175_ = lean_ctor_get(v_s_5174_, 4);
lean_inc(v_errorMsg_5175_);
v___x_5176_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5175_, v___x_5169_);
lean_dec(v_errorMsg_5175_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_Parser_ParserState_restore(v_s_5174_, v_iniSz_5173_, v_pos_5167_);
lean_dec(v_iniSz_5173_);
return v___x_5177_;
}
else
{
lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_dec(v_pos_5167_);
v___x_5178_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5179_ = lean_unsigned_to_nat(1u);
v___x_5180_ = lean_nat_sub(v_iniSz_5173_, v___x_5179_);
lean_dec(v_iniSz_5173_);
v___x_5181_ = l_Lean_Parser_ParserState_mkNode(v_s_5174_, v___x_5178_, v___x_5180_);
lean_dec(v___x_5180_);
return v___x_5181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v_toInputContext_5185_; lean_object* v_s_5186_; lean_object* v_pos_5187_; lean_object* v_inputString_5188_; uint32_t v___x_5189_; uint32_t v___x_5190_; uint8_t v___x_5191_; 
v_toInputContext_5185_ = lean_ctor_get(v___y_5183_, 0);
lean_inc_ref(v___y_5183_);
v_s_5186_ = lean_apply_2(v_fn_5182_, v___y_5183_, v___y_5184_);
v_pos_5187_ = lean_ctor_get(v_s_5186_, 2);
lean_inc(v_pos_5187_);
v_inputString_5188_ = lean_ctor_get(v_toInputContext_5185_, 0);
v___x_5189_ = lean_string_utf8_get(v_inputString_5188_, v_pos_5187_);
lean_dec(v_pos_5187_);
v___x_5190_ = 37;
v___x_5191_ = lean_uint32_dec_eq(v___x_5189_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_dec_ref(v___y_5183_);
return v_s_5186_;
}
else
{
lean_object* v___x_5192_; 
v___x_5192_ = l_Lean_Parser_tokenAntiquotFn(v___y_5183_, v_s_5186_);
return v___x_5192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5193_){
_start:
{
lean_object* v_info_5194_; lean_object* v_fn_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5203_; 
v_info_5194_ = lean_ctor_get(v_p_5193_, 0);
v_fn_5195_ = lean_ctor_get(v_p_5193_, 1);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_p_5193_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5197_ = v_p_5193_;
v_isShared_5198_ = v_isSharedCheck_5203_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_fn_5195_);
lean_inc(v_info_5194_);
lean_dec(v_p_5193_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5203_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___f_5199_; lean_object* v___x_5201_; 
v___f_5199_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5199_, 0, v_fn_5195_);
if (v_isShared_5198_ == 0)
{
lean_ctor_set(v___x_5197_, 1, v___f_5199_);
v___x_5201_ = v___x_5197_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_info_5194_);
lean_ctor_set(v_reuseFailAlloc_5202_, 1, v___f_5199_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5204_){
_start:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5205_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5204_);
v___x_5206_ = l_Lean_Parser_tokenWithAntiquot(v___x_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5209_, uint8_t v_includeIdent_5210_){
_start:
{
lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5211_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5209_, v_includeIdent_5210_);
v___x_5212_ = l_Lean_Parser_tokenWithAntiquot(v___x_5211_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5213_, lean_object* v_includeIdent_5214_){
_start:
{
uint8_t v_includeIdent_boxed_5215_; lean_object* v_res_5216_; 
v_includeIdent_boxed_5215_ = lean_unbox(v_includeIdent_5214_);
v_res_5216_ = l_Lean_Parser_nonReservedSymbol(v_sym_5213_, v_includeIdent_boxed_5215_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5217_, lean_object* v_asciiSym_5218_){
_start:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5219_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5217_, v_asciiSym_5218_);
v___x_5220_ = l_Lean_Parser_tokenWithAntiquot(v___x_5219_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5221_, lean_object* v_asciiSym_5222_, uint8_t v_preserveForPP_5223_){
_start:
{
lean_object* v___x_5224_; 
v___x_5224_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5221_, v_asciiSym_5222_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5225_, lean_object* v_asciiSym_5226_, lean_object* v_preserveForPP_5227_){
_start:
{
uint8_t v_preserveForPP_boxed_5228_; lean_object* v_res_5229_; 
v_preserveForPP_boxed_5228_ = lean_unbox(v_preserveForPP_5227_);
v_res_5229_ = l_Lean_Parser_unicodeSymbol(v_sym_5225_, v_asciiSym_5226_, v_preserveForPP_boxed_5228_);
return v_res_5229_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5230_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5231_ = l_Lean_Parser_symbol(v___x_5230_);
return v___x_5231_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5232_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5233_ = lean_box(0);
v___x_5234_ = l_Lean_Parser_setExpected(v___x_5233_, v___x_5232_);
return v___x_5234_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5235_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5236_ = l_Lean_Parser_checkNoWsBefore(v___x_5235_);
return v___x_5236_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5237_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5238_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5239_ = l_Lean_Parser_andthen(v___x_5238_, v___x_5237_);
return v___x_5239_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5241_ = l_Lean_Parser_manyNoAntiquot(v___x_5240_);
return v___x_5241_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5243_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5244_ = l_Lean_Parser_checkNoWsBefore(v___x_5243_);
return v___x_5244_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5253_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5254_ = l_Lean_Parser_symbol(v___x_5253_);
return v___x_5254_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5255_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5256_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5257_ = l_Lean_Parser_andthen(v___x_5256_, v___x_5255_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5261_, lean_object* v_kind_5262_, uint8_t v_anonymous_5263_, uint8_t v_isPseudoKind_5264_){
_start:
{
lean_object* v___y_5266_; lean_object* v___y_5267_; lean_object* v___y_5280_; 
if (v_isPseudoKind_5264_ == 0)
{
lean_object* v___x_5298_; 
v___x_5298_ = lean_box(0);
v___y_5280_ = v___x_5298_;
goto v___jp_5279_;
}
else
{
lean_object* v___x_5299_; 
v___x_5299_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5280_ = v___x_5299_;
goto v___jp_5279_;
}
v___jp_5265_:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5268_ = l_Lean_Parser_maxPrec;
v___x_5269_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5270_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5271_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5272_ = l_Lean_Parser_antiquotExpr;
v___x_5273_ = l_Lean_Parser_andthen(v___x_5272_, v___y_5267_);
v___x_5274_ = l_Lean_Parser_andthen(v___x_5271_, v___x_5273_);
v___x_5275_ = l_Lean_Parser_andthen(v___x_5270_, v___x_5274_);
v___x_5276_ = l_Lean_Parser_andthen(v___x_5269_, v___x_5275_);
v___x_5277_ = l_Lean_Parser_atomic(v___x_5276_);
v___x_5278_ = l_Lean_Parser_leadingNode(v___y_5266_, v___x_5268_, v___x_5277_);
return v___x_5278_;
}
v___jp_5279_:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v_kind_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v_nameP_5295_; 
lean_inc(v___y_5280_);
v___x_5281_ = l_Lean_Name_append(v_kind_5262_, v___y_5280_);
v___x_5282_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5283_ = l_Lean_Name_append(v___x_5281_, v___x_5282_);
v___x_5284_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5285_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5286_ = lean_string_append(v___x_5285_, v_name_5261_);
v___x_5287_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5288_ = lean_string_append(v___x_5286_, v___x_5287_);
v___x_5289_ = l_Lean_Parser_checkNoWsBefore(v___x_5288_);
v___x_5290_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5291_ = 0;
v___x_5292_ = l_Lean_Parser_nonReservedSymbol(v_name_5261_, v___x_5291_);
v___x_5293_ = l_Lean_Parser_andthen(v___x_5290_, v___x_5292_);
v___x_5294_ = l_Lean_Parser_andthen(v___x_5289_, v___x_5293_);
v_nameP_5295_ = l_Lean_Parser_node(v___x_5284_, v___x_5294_);
if (v_anonymous_5263_ == 0)
{
v___y_5266_ = v_kind_5283_;
v___y_5267_ = v_nameP_5295_;
goto v___jp_5265_;
}
else
{
lean_object* v___x_5296_; lean_object* v___x_5297_; 
v___x_5296_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5297_ = l_Lean_Parser_orelse(v_nameP_5295_, v___x_5296_);
v___y_5266_ = v_kind_5283_;
v___y_5267_ = v___x_5297_;
goto v___jp_5265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5300_, lean_object* v_kind_5301_, lean_object* v_anonymous_5302_, lean_object* v_isPseudoKind_5303_){
_start:
{
uint8_t v_anonymous_boxed_5304_; uint8_t v_isPseudoKind_boxed_5305_; lean_object* v_res_5306_; 
v_anonymous_boxed_5304_ = lean_unbox(v_anonymous_5302_);
v_isPseudoKind_boxed_5305_ = lean_unbox(v_isPseudoKind_5303_);
v_res_5306_ = l_Lean_Parser_mkAntiquot(v_name_5300_, v_kind_5301_, v_anonymous_boxed_5304_, v_isPseudoKind_boxed_5305_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5314_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5315_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5316_ = l_Lean_addBuiltinDocString(v___x_5314_, v___x_5315_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5317_){
_start:
{
lean_object* v_res_5318_; 
v_res_5318_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5319_, lean_object* v_p_5320_, uint8_t v_isCatAntiquot_5321_, lean_object* v_c_5322_, lean_object* v_s_5323_){
_start:
{
lean_object* v_toInputContext_5324_; lean_object* v_pos_5325_; lean_object* v_inputString_5326_; uint32_t v___x_5327_; uint32_t v___x_5328_; uint8_t v___x_5329_; 
v_toInputContext_5324_ = lean_ctor_get(v_c_5322_, 0);
v_pos_5325_ = lean_ctor_get(v_s_5323_, 2);
v_inputString_5326_ = lean_ctor_get(v_toInputContext_5324_, 0);
v___x_5327_ = lean_string_utf8_get(v_inputString_5326_, v_pos_5325_);
v___x_5328_ = 36;
v___x_5329_ = lean_uint32_dec_eq(v___x_5327_, v___x_5328_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; 
lean_dec_ref(v_antiquotP_5319_);
v___x_5330_ = lean_apply_2(v_p_5320_, v_c_5322_, v_s_5323_);
return v___x_5330_;
}
else
{
if (v_isCatAntiquot_5321_ == 0)
{
uint8_t v___x_5331_; lean_object* v___x_5332_; 
v___x_5331_ = 1;
v___x_5332_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5319_, v_p_5320_, v___x_5331_, v_c_5322_, v_s_5323_);
return v___x_5332_;
}
else
{
uint8_t v___x_5333_; lean_object* v___x_5334_; 
v___x_5333_ = 0;
v___x_5334_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5319_, v_p_5320_, v___x_5333_, v_c_5322_, v_s_5323_);
return v___x_5334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5335_, lean_object* v_p_5336_, lean_object* v_isCatAntiquot_5337_, lean_object* v_c_5338_, lean_object* v_s_5339_){
_start:
{
uint8_t v_isCatAntiquot_boxed_5340_; lean_object* v_res_5341_; 
v_isCatAntiquot_boxed_5340_ = lean_unbox(v_isCatAntiquot_5337_);
v_res_5341_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5335_, v_p_5336_, v_isCatAntiquot_boxed_5340_, v_c_5338_, v_s_5339_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5342_, lean_object* v_p_5343_){
_start:
{
lean_object* v_info_5344_; lean_object* v_fn_5345_; lean_object* v_info_5346_; lean_object* v_fn_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5358_; 
v_info_5344_ = lean_ctor_get(v_antiquotP_5342_, 0);
lean_inc_ref(v_info_5344_);
v_fn_5345_ = lean_ctor_get(v_antiquotP_5342_, 1);
lean_inc_ref(v_fn_5345_);
lean_dec_ref(v_antiquotP_5342_);
v_info_5346_ = lean_ctor_get(v_p_5343_, 0);
v_fn_5347_ = lean_ctor_get(v_p_5343_, 1);
v_isSharedCheck_5358_ = !lean_is_exclusive(v_p_5343_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5349_ = v_p_5343_;
v_isShared_5350_ = v_isSharedCheck_5358_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_fn_5347_);
lean_inc(v_info_5346_);
lean_dec(v_p_5343_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5358_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5351_; uint8_t v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5356_; 
v___x_5351_ = l_Lean_Parser_orelseInfo(v_info_5344_, v_info_5346_);
v___x_5352_ = 0;
v___x_5353_ = lean_box(v___x_5352_);
v___x_5354_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5354_, 0, v_fn_5345_);
lean_closure_set(v___x_5354_, 1, v_fn_5347_);
lean_closure_set(v___x_5354_, 2, v___x_5353_);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5354_);
lean_ctor_set(v___x_5349_, 0, v___x_5351_);
v___x_5356_ = v___x_5349_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5357_, 1, v___x_5354_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5366_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5367_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5368_ = l_Lean_addBuiltinDocString(v___x_5366_, v___x_5367_);
return v___x_5368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5371_){
_start:
{
lean_object* v_fn_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5380_; 
v_fn_5372_ = lean_ctor_get(v_p_5371_, 1);
v_isSharedCheck_5380_ = !lean_is_exclusive(v_p_5371_);
if (v_isSharedCheck_5380_ == 0)
{
lean_object* v_unused_5381_; 
v_unused_5381_ = lean_ctor_get(v_p_5371_, 0);
lean_dec(v_unused_5381_);
v___x_5374_ = v_p_5371_;
v_isShared_5375_ = v_isSharedCheck_5380_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_fn_5372_);
lean_dec(v_p_5371_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5380_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v___x_5376_; lean_object* v___x_5378_; 
v___x_5376_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v___x_5376_);
v___x_5378_ = v___x_5374_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5379_, 1, v_fn_5372_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5385_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5386_ = l_Lean_Parser_symbol(v___x_5385_);
return v___x_5386_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5387_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5388_ = l_Lean_Parser_symbol(v___x_5387_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5389_, lean_object* v_p_5390_, lean_object* v_suffix_5391_){
_start:
{
lean_object* v___x_5392_; lean_object* v_kind_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5392_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5393_ = l_Lean_Name_append(v_kind_5389_, v___x_5392_);
v___x_5394_ = l_Lean_Parser_maxPrec;
v___x_5395_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5396_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5397_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5398_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5399_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5400_ = l_Lean_Parser_node(v___x_5399_, v_p_5390_);
v___x_5401_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5402_ = l_Lean_Parser_andthen(v___x_5401_, v_suffix_5391_);
v___x_5403_ = l_Lean_Parser_andthen(v___x_5400_, v___x_5402_);
v___x_5404_ = l_Lean_Parser_andthen(v___x_5398_, v___x_5403_);
v___x_5405_ = l_Lean_Parser_andthen(v___x_5397_, v___x_5404_);
v___x_5406_ = l_Lean_Parser_andthen(v___x_5396_, v___x_5405_);
v___x_5407_ = l_Lean_Parser_andthen(v___x_5395_, v___x_5406_);
v___x_5408_ = l_Lean_Parser_atomic(v___x_5407_);
v___x_5409_ = l_Lean_Parser_leadingNode(v_kind_5393_, v___x_5394_, v___x_5408_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5417_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5418_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5419_ = l_Lean_addBuiltinDocString(v___x_5417_, v___x_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5425_, lean_object* v_suffix_5426_, lean_object* v_c_5427_, lean_object* v_s_5428_){
_start:
{
lean_object* v_pos_5429_; lean_object* v_iniSz_5430_; lean_object* v_s_5431_; lean_object* v_stxStack_5432_; lean_object* v_errorMsg_5433_; lean_object* v___x_5434_; uint8_t v___x_5435_; 
v_pos_5429_ = lean_ctor_get(v_s_5428_, 2);
lean_inc(v_pos_5429_);
v_iniSz_5430_ = l_Lean_Parser_ParserState_stackSize(v_s_5428_);
v_s_5431_ = lean_apply_2(v_suffix_5426_, v_c_5427_, v_s_5428_);
v_stxStack_5432_ = lean_ctor_get(v_s_5431_, 0);
lean_inc_ref(v_stxStack_5432_);
v_errorMsg_5433_ = lean_ctor_get(v_s_5431_, 4);
lean_inc(v_errorMsg_5433_);
v___x_5434_ = lean_box(0);
v___x_5435_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5433_, v___x_5434_);
lean_dec(v_errorMsg_5433_);
if (v___x_5435_ == 0)
{
lean_object* v___x_5436_; 
lean_dec_ref(v_stxStack_5432_);
lean_dec(v_kind_5425_);
v___x_5436_ = l_Lean_Parser_ParserState_restore(v_s_5431_, v_iniSz_5430_, v_pos_5429_);
lean_dec(v_iniSz_5430_);
return v___x_5436_;
}
else
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec(v_iniSz_5430_);
lean_dec(v_pos_5429_);
v___x_5437_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5438_ = l_Lean_Name_append(v_kind_5425_, v___x_5437_);
v___x_5439_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5432_);
lean_dec_ref(v_stxStack_5432_);
v___x_5440_ = lean_unsigned_to_nat(2u);
v___x_5441_ = lean_nat_sub(v___x_5439_, v___x_5440_);
lean_dec(v___x_5439_);
v___x_5442_ = l_Lean_Parser_ParserState_mkNode(v_s_5431_, v___x_5438_, v___x_5441_);
lean_dec(v___x_5441_);
return v___x_5442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5443_, lean_object* v_kind_5444_, lean_object* v_fn_5445_, lean_object* v_c_5446_, lean_object* v_s_5447_){
_start:
{
lean_object* v_s_5448_; lean_object* v_stxStack_5449_; lean_object* v_errorMsg_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; 
lean_inc_ref(v_c_5446_);
v_s_5448_ = lean_apply_2(v_fn_5443_, v_c_5446_, v_s_5447_);
v_stxStack_5449_ = lean_ctor_get(v_s_5448_, 0);
lean_inc_ref(v_stxStack_5449_);
v_errorMsg_5450_ = lean_ctor_get(v_s_5448_, 4);
lean_inc(v_errorMsg_5450_);
v___x_5451_ = lean_box(0);
v___x_5452_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5450_, v___x_5451_);
lean_dec(v_errorMsg_5450_);
if (v___x_5452_ == 0)
{
lean_dec_ref(v_stxStack_5449_);
lean_dec_ref(v_c_5446_);
lean_dec_ref(v_fn_5445_);
lean_dec(v_kind_5444_);
return v_s_5448_;
}
else
{
lean_object* v___x_5453_; uint8_t v___x_5454_; 
v___x_5453_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5449_);
lean_dec_ref(v_stxStack_5449_);
v___x_5454_ = l_Lean_Syntax_isAntiquots(v___x_5453_);
if (v___x_5454_ == 0)
{
lean_dec_ref(v_c_5446_);
lean_dec_ref(v_fn_5445_);
lean_dec(v_kind_5444_);
return v_s_5448_;
}
else
{
lean_object* v___x_5455_; 
v___x_5455_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5444_, v_fn_5445_, v_c_5446_, v_s_5448_);
return v___x_5455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5456_, lean_object* v_p_5457_, lean_object* v_suffix_5458_){
_start:
{
lean_object* v_info_5459_; lean_object* v_fn_5460_; lean_object* v_info_5461_; lean_object* v_fn_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5471_; 
v_info_5459_ = lean_ctor_get(v_p_5457_, 0);
lean_inc_ref(v_info_5459_);
v_fn_5460_ = lean_ctor_get(v_p_5457_, 1);
lean_inc_ref(v_fn_5460_);
lean_dec_ref(v_p_5457_);
v_info_5461_ = lean_ctor_get(v_suffix_5458_, 0);
v_fn_5462_ = lean_ctor_get(v_suffix_5458_, 1);
v_isSharedCheck_5471_ = !lean_is_exclusive(v_suffix_5458_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5464_ = v_suffix_5458_;
v_isShared_5465_ = v_isSharedCheck_5471_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_fn_5462_);
lean_inc(v_info_5461_);
lean_dec(v_suffix_5458_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5471_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___f_5466_; lean_object* v___x_5467_; lean_object* v___x_5469_; 
v___f_5466_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5466_, 0, v_fn_5460_);
lean_closure_set(v___f_5466_, 1, v_kind_5456_);
lean_closure_set(v___f_5466_, 2, v_fn_5462_);
v___x_5467_ = l_Lean_Parser_andthenInfo(v_info_5459_, v_info_5461_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 1, v___f_5466_);
lean_ctor_set(v___x_5464_, 0, v___x_5467_);
v___x_5469_ = v___x_5464_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5467_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___f_5466_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5479_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5480_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5481_ = l_Lean_addBuiltinDocString(v___x_5479_, v___x_5480_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5482_){
_start:
{
lean_object* v_res_5483_; 
v_res_5483_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5484_, lean_object* v_p_5485_, lean_object* v_suffix_5486_){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
lean_inc_ref(v_p_5485_);
v___x_5487_ = l_Lean_Parser_withoutInfo(v_p_5485_);
lean_inc_ref(v_suffix_5486_);
lean_inc(v_kind_5484_);
v___x_5488_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5484_, v___x_5487_, v_suffix_5486_);
v___x_5489_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5484_, v_p_5485_, v_suffix_5486_);
v___x_5490_ = l_Lean_Parser_withAntiquot(v___x_5488_, v___x_5489_);
return v___x_5490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5491_, lean_object* v_kind_5492_, lean_object* v_p_5493_, uint8_t v_anonymous_5494_){
_start:
{
uint8_t v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5495_ = 0;
lean_inc(v_kind_5492_);
v___x_5496_ = l_Lean_Parser_mkAntiquot(v_name_5491_, v_kind_5492_, v_anonymous_5494_, v___x_5495_);
v___x_5497_ = l_Lean_Parser_node(v_kind_5492_, v_p_5493_);
v___x_5498_ = l_Lean_Parser_withAntiquot(v___x_5496_, v___x_5497_);
return v___x_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5499_, lean_object* v_kind_5500_, lean_object* v_p_5501_, lean_object* v_anonymous_5502_){
_start:
{
uint8_t v_anonymous_boxed_5503_; lean_object* v_res_5504_; 
v_anonymous_boxed_5503_ = lean_unbox(v_anonymous_5502_);
v_res_5504_ = l_Lean_Parser_nodeWithAntiquot(v_name_5499_, v_kind_5500_, v_p_5501_, v_anonymous_boxed_5503_);
return v_res_5504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5509_, lean_object* v_sep_5510_){
_start:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v_str_5515_; lean_object* v_startInclusive_5516_; lean_object* v_endExclusive_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5511_ = lean_unsigned_to_nat(0u);
v___x_5512_ = lean_string_utf8_byte_size(v_sep_5510_);
v___x_5513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5513_, 0, v_sep_5510_);
lean_ctor_set(v___x_5513_, 1, v___x_5511_);
lean_ctor_set(v___x_5513_, 2, v___x_5512_);
v___x_5514_ = l_String_Slice_trimAscii(v___x_5513_);
v_str_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc_ref(v_str_5515_);
v_startInclusive_5516_ = lean_ctor_get(v___x_5514_, 1);
lean_inc(v_startInclusive_5516_);
v_endExclusive_5517_ = lean_ctor_get(v___x_5514_, 2);
lean_inc(v_endExclusive_5517_);
lean_dec_ref(v___x_5514_);
v___x_5518_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5519_ = lean_string_utf8_extract(v_str_5515_, v_startInclusive_5516_, v_endExclusive_5517_);
lean_dec(v_endExclusive_5517_);
lean_dec(v_startInclusive_5516_);
lean_dec_ref(v_str_5515_);
v___x_5520_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5521_ = lean_string_append(v___x_5519_, v___x_5520_);
v___x_5522_ = l_Lean_Parser_symbol(v___x_5521_);
v___x_5523_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5518_, v_p_5509_, v___x_5522_);
return v___x_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5524_, lean_object* v_sep_5525_, lean_object* v_psep_5526_, uint8_t v_allowTrailingSep_5527_){
_start:
{
lean_object* v___x_5528_; lean_object* v___x_5529_; 
v___x_5528_ = l_Lean_Parser_sepByElemParser(v_p_5524_, v_sep_5525_);
v___x_5529_ = l_Lean_Parser_sepByNoAntiquot(v___x_5528_, v_psep_5526_, v_allowTrailingSep_5527_);
return v___x_5529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5530_, lean_object* v_sep_5531_, lean_object* v_psep_5532_, lean_object* v_allowTrailingSep_5533_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5534_; lean_object* v_res_5535_; 
v_allowTrailingSep_boxed_5534_ = lean_unbox(v_allowTrailingSep_5533_);
v_res_5535_ = l_Lean_Parser_sepBy(v_p_5530_, v_sep_5531_, v_psep_5532_, v_allowTrailingSep_boxed_5534_);
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5536_, lean_object* v_sep_5537_, lean_object* v_psep_5538_, uint8_t v_allowTrailingSep_5539_){
_start:
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5540_ = l_Lean_Parser_sepByElemParser(v_p_5536_, v_sep_5537_);
v___x_5541_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5540_, v_psep_5538_, v_allowTrailingSep_5539_);
return v___x_5541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5542_, lean_object* v_sep_5543_, lean_object* v_psep_5544_, lean_object* v_allowTrailingSep_5545_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5546_; lean_object* v_res_5547_; 
v_allowTrailingSep_boxed_5546_ = lean_unbox(v_allowTrailingSep_5545_);
v_res_5547_ = l_Lean_Parser_sepBy1(v_p_5542_, v_sep_5543_, v_psep_5544_, v_allowTrailingSep_boxed_5546_);
return v_res_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5548_, lean_object* v_iniSz_5549_){
_start:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
v___x_5550_ = l_Lean_Parser_ParserState_stackSize(v_s_5548_);
v___x_5551_ = lean_unsigned_to_nat(1u);
v___x_5552_ = lean_nat_add(v_iniSz_5549_, v___x_5551_);
v___x_5553_ = lean_nat_dec_eq(v___x_5550_, v___x_5552_);
lean_dec(v___x_5552_);
lean_dec(v___x_5550_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5554_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5555_ = l_Lean_Parser_ParserState_mkNode(v_s_5548_, v___x_5554_, v_iniSz_5549_);
return v___x_5555_;
}
else
{
return v_s_5548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5556_, lean_object* v_iniSz_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5556_, v_iniSz_5557_);
lean_dec(v_iniSz_5557_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5559_, lean_object* v_tables_5560_, uint8_t v_behavior_5561_, lean_object* v_c_5562_, lean_object* v_s_5563_){
_start:
{
lean_object* v_leadingTable_5564_; lean_object* v_leadingParsers_5565_; lean_object* v_iniSz_5566_; lean_object* v___x_5567_; lean_object* v_fst_5568_; lean_object* v_snd_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5591_; 
v_leadingTable_5564_ = lean_ctor_get(v_tables_5560_, 0);
lean_inc(v_leadingTable_5564_);
v_leadingParsers_5565_ = lean_ctor_get(v_tables_5560_, 1);
lean_inc(v_leadingParsers_5565_);
lean_dec_ref(v_tables_5560_);
v_iniSz_5566_ = l_Lean_Parser_ParserState_stackSize(v_s_5563_);
lean_inc_ref(v_c_5562_);
v___x_5567_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5564_, v_c_5562_, v_s_5563_, v_behavior_5561_);
lean_dec(v_leadingTable_5564_);
v_fst_5568_ = lean_ctor_get(v___x_5567_, 0);
v_snd_5569_ = lean_ctor_get(v___x_5567_, 1);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5571_ = v___x_5567_;
v_isShared_5572_ = v_isSharedCheck_5591_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_snd_5569_);
lean_inc(v_fst_5568_);
lean_dec(v___x_5567_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5591_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v_errorMsg_5573_; lean_object* v___x_5574_; uint8_t v___x_5575_; 
v_errorMsg_5573_ = lean_ctor_get(v_fst_5568_, 4);
v___x_5574_ = lean_box(0);
v___x_5575_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5573_, v___x_5574_);
if (v___x_5575_ == 0)
{
lean_del_object(v___x_5571_);
lean_dec(v_snd_5569_);
lean_dec(v_iniSz_5566_);
lean_dec(v_leadingParsers_5565_);
lean_dec_ref(v_c_5562_);
lean_dec(v_kind_5559_);
return v_fst_5568_;
}
else
{
lean_object* v_ps_5576_; uint8_t v___x_5577_; 
v_ps_5576_ = l_List_appendTR___redArg(v_leadingParsers_5565_, v_snd_5569_);
v___x_5577_ = l_List_isEmpty___redArg(v_ps_5576_);
if (v___x_5577_ == 0)
{
lean_object* v_s_5578_; lean_object* v___x_5579_; 
lean_del_object(v___x_5571_);
lean_dec(v_kind_5559_);
v_s_5578_ = l_Lean_Parser_longestMatchFn(v___x_5574_, v_ps_5576_, v_c_5562_, v_fst_5568_);
v___x_5579_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5578_, v_iniSz_5566_);
lean_dec(v_iniSz_5566_);
return v___x_5579_;
}
else
{
lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5583_; 
lean_dec(v_ps_5576_);
lean_dec(v_iniSz_5566_);
v___x_5580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5559_, v___x_5577_);
v___x_5581_ = lean_box(0);
lean_inc_ref(v___x_5580_);
if (v_isShared_5572_ == 0)
{
lean_ctor_set_tag(v___x_5571_, 1);
lean_ctor_set(v___x_5571_, 1, v___x_5581_);
lean_ctor_set(v___x_5571_, 0, v___x_5580_);
v___x_5583_ = v___x_5571_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5580_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v_s_5584_; lean_object* v_errorMsg_5588_; uint8_t v___x_5589_; 
v_s_5584_ = l_Lean_Parser_tokenFn(v___x_5583_, v_c_5562_, v_fst_5568_);
v_errorMsg_5588_ = lean_ctor_get(v_s_5584_, 4);
lean_inc(v_errorMsg_5588_);
v___x_5589_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5588_, v___x_5574_);
lean_dec(v_errorMsg_5588_);
if (v___x_5589_ == 0)
{
if (v___x_5577_ == 0)
{
goto v___jp_5585_;
}
else
{
lean_dec_ref(v___x_5580_);
return v_s_5584_;
}
}
else
{
goto v___jp_5585_;
}
v___jp_5585_:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = lean_unsigned_to_nat(0u);
v___x_5587_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5584_, v___x_5580_, v___x_5586_);
return v___x_5587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5592_, lean_object* v_tables_5593_, lean_object* v_behavior_5594_, lean_object* v_c_5595_, lean_object* v_s_5596_){
_start:
{
uint8_t v_behavior_boxed_5597_; lean_object* v_res_5598_; 
v_behavior_boxed_5597_ = lean_unbox(v_behavior_5594_);
v_res_5598_ = l_Lean_Parser_leadingParserAux(v_kind_5592_, v_tables_5593_, v_behavior_boxed_5597_, v_c_5595_, v_s_5596_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5599_, lean_object* v_tables_5600_, uint8_t v_behavior_5601_, lean_object* v_antiquotParser_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_){
_start:
{
lean_object* v___x_5605_; lean_object* v___x_5606_; uint8_t v___x_5607_; lean_object* v___x_5608_; 
v___x_5605_ = lean_box(v_behavior_5601_);
v___x_5606_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5606_, 0, v_kind_5599_);
lean_closure_set(v___x_5606_, 1, v_tables_5600_);
lean_closure_set(v___x_5606_, 2, v___x_5605_);
v___x_5607_ = 1;
v___x_5608_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5602_, v___x_5606_, v___x_5607_, v_a_5603_, v_a_5604_);
return v___x_5608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5609_, lean_object* v_tables_5610_, lean_object* v_behavior_5611_, lean_object* v_antiquotParser_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_){
_start:
{
uint8_t v_behavior_boxed_5615_; lean_object* v_res_5616_; 
v_behavior_boxed_5615_ = lean_unbox(v_behavior_5611_);
v_res_5616_ = l_Lean_Parser_leadingParser(v_kind_5609_, v_tables_5610_, v_behavior_boxed_5615_, v_antiquotParser_5612_, v_a_5613_, v_a_5614_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5617_, lean_object* v_left_5618_, lean_object* v_ps_5619_, lean_object* v_c_5620_, lean_object* v_s_5621_){
_start:
{
lean_object* v_trailingParsers_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; 
v_trailingParsers_5622_ = lean_ctor_get(v_tables_5617_, 3);
lean_inc(v_trailingParsers_5622_);
lean_dec_ref(v_tables_5617_);
v___x_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5623_, 0, v_left_5618_);
v___x_5624_ = l_List_appendTR___redArg(v_ps_5619_, v_trailingParsers_5622_);
v___x_5625_ = l_Lean_Parser_longestMatchFn(v___x_5623_, v___x_5624_, v_c_5620_, v_s_5621_);
return v___x_5625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5626_, lean_object* v_c_5627_, lean_object* v_s_5628_){
_start:
{
lean_object* v_pos_5629_; lean_object* v_trailingTable_5630_; lean_object* v_trailingParsers_5631_; lean_object* v_iniSz_5632_; uint8_t v___x_5633_; lean_object* v___x_5634_; lean_object* v_fst_5635_; lean_object* v_snd_5636_; lean_object* v_stxStack_5637_; lean_object* v_errorMsg_5638_; uint8_t v___y_5640_; lean_object* v___x_5654_; uint8_t v___x_5655_; 
v_pos_5629_ = lean_ctor_get(v_s_5628_, 2);
lean_inc(v_pos_5629_);
v_trailingTable_5630_ = lean_ctor_get(v_tables_5626_, 2);
v_trailingParsers_5631_ = lean_ctor_get(v_tables_5626_, 3);
v_iniSz_5632_ = l_Lean_Parser_ParserState_stackSize(v_s_5628_);
v___x_5633_ = 0;
lean_inc_ref(v_c_5627_);
v___x_5634_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5630_, v_c_5627_, v_s_5628_, v___x_5633_);
v_fst_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc(v_fst_5635_);
v_snd_5636_ = lean_ctor_get(v___x_5634_, 1);
lean_inc(v_snd_5636_);
lean_dec_ref(v___x_5634_);
v_stxStack_5637_ = lean_ctor_get(v_fst_5635_, 0);
v_errorMsg_5638_ = lean_ctor_get(v_fst_5635_, 4);
v___x_5654_ = lean_box(0);
v___x_5655_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5638_, v___x_5654_);
if (v___x_5655_ == 0)
{
lean_object* v___x_5656_; 
lean_dec(v_snd_5636_);
lean_dec_ref(v_c_5627_);
lean_dec_ref(v_tables_5626_);
v___x_5656_ = l_Lean_Parser_ParserState_restore(v_fst_5635_, v_iniSz_5632_, v_pos_5629_);
lean_dec(v_iniSz_5632_);
return v___x_5656_;
}
else
{
uint8_t v___x_5657_; 
v___x_5657_ = l_List_isEmpty___redArg(v_snd_5636_);
if (v___x_5657_ == 0)
{
v___y_5640_ = v___x_5657_;
goto v___jp_5639_;
}
else
{
uint8_t v___x_5658_; 
v___x_5658_ = l_List_isEmpty___redArg(v_trailingParsers_5631_);
v___y_5640_ = v___x_5658_;
goto v___jp_5639_;
}
}
v___jp_5639_:
{
if (v___y_5640_ == 0)
{
lean_object* v_left_5641_; lean_object* v_s_5642_; lean_object* v_s_5643_; lean_object* v_pos_5644_; lean_object* v_errorMsg_5645_; lean_object* v___x_5646_; uint8_t v___x_5647_; 
v_left_5641_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5637_);
v_s_5642_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5635_);
lean_inc_ref(v_c_5627_);
lean_inc(v_left_5641_);
lean_inc_ref(v_tables_5626_);
v_s_5643_ = l_Lean_Parser_trailingLoopStep(v_tables_5626_, v_left_5641_, v_snd_5636_, v_c_5627_, v_s_5642_);
v_pos_5644_ = lean_ctor_get(v_s_5643_, 2);
lean_inc(v_pos_5644_);
v_errorMsg_5645_ = lean_ctor_get(v_s_5643_, 4);
lean_inc(v_errorMsg_5645_);
v___x_5646_ = lean_box(0);
v___x_5647_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5645_, v___x_5646_);
lean_dec(v_errorMsg_5645_);
if (v___x_5647_ == 0)
{
uint8_t v___x_5648_; 
lean_dec_ref(v_c_5627_);
lean_dec_ref(v_tables_5626_);
v___x_5648_ = lean_nat_dec_eq(v_pos_5644_, v_pos_5629_);
lean_dec(v_pos_5644_);
if (v___x_5648_ == 0)
{
lean_dec(v_left_5641_);
lean_dec(v_iniSz_5632_);
lean_dec(v_pos_5629_);
return v_s_5643_;
}
else
{
lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v___x_5649_ = lean_unsigned_to_nat(1u);
v___x_5650_ = lean_nat_sub(v_iniSz_5632_, v___x_5649_);
lean_dec(v_iniSz_5632_);
v___x_5651_ = l_Lean_Parser_ParserState_restore(v_s_5643_, v___x_5650_, v_pos_5629_);
lean_dec(v___x_5650_);
v___x_5652_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5651_, v_left_5641_);
return v___x_5652_;
}
}
else
{
lean_dec(v_pos_5644_);
lean_dec(v_left_5641_);
lean_dec(v_iniSz_5632_);
lean_dec(v_pos_5629_);
v_s_5628_ = v_s_5643_;
goto _start;
}
}
else
{
lean_dec(v_snd_5636_);
lean_dec(v_iniSz_5632_);
lean_dec(v_pos_5629_);
lean_dec_ref(v_c_5627_);
lean_dec_ref(v_tables_5626_);
return v_fst_5635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5659_, lean_object* v_tables_5660_, uint8_t v_behavior_5661_, lean_object* v_antiquotParser_5662_, lean_object* v_c_5663_, lean_object* v_s_5664_){
_start:
{
lean_object* v_s_5665_; lean_object* v_errorMsg_5666_; lean_object* v___x_5667_; uint8_t v___x_5668_; 
lean_inc_ref(v_c_5663_);
lean_inc_ref(v_tables_5660_);
v_s_5665_ = l_Lean_Parser_leadingParser(v_kind_5659_, v_tables_5660_, v_behavior_5661_, v_antiquotParser_5662_, v_c_5663_, v_s_5664_);
v_errorMsg_5666_ = lean_ctor_get(v_s_5665_, 4);
lean_inc(v_errorMsg_5666_);
v___x_5667_ = lean_box(0);
v___x_5668_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5666_, v___x_5667_);
lean_dec(v_errorMsg_5666_);
if (v___x_5668_ == 0)
{
lean_dec_ref(v_c_5663_);
lean_dec_ref(v_tables_5660_);
return v_s_5665_;
}
else
{
lean_object* v___x_5669_; 
v___x_5669_ = l_Lean_Parser_trailingLoop(v_tables_5660_, v_c_5663_, v_s_5665_);
return v___x_5669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5670_, lean_object* v_tables_5671_, lean_object* v_behavior_5672_, lean_object* v_antiquotParser_5673_, lean_object* v_c_5674_, lean_object* v_s_5675_){
_start:
{
uint8_t v_behavior_boxed_5676_; lean_object* v_res_5677_; 
v_behavior_boxed_5676_ = lean_unbox(v_behavior_5672_);
v_res_5677_ = l_Lean_Parser_prattParser(v_kind_5670_, v_tables_5671_, v_behavior_boxed_5676_, v_antiquotParser_5673_, v_c_5674_, v_s_5675_);
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5682_, lean_object* v_s_5683_){
_start:
{
lean_object* v_toInputContext_5684_; lean_object* v_pos_5685_; lean_object* v_inputString_5686_; lean_object* v___f_5687_; lean_object* v_initStackSz_5688_; uint32_t v_curr_5693_; uint8_t v___y_5695_; uint32_t v___x_5701_; uint8_t v___x_5702_; 
v_toInputContext_5684_ = lean_ctor_get(v_c_5682_, 0);
v_pos_5685_ = lean_ctor_get(v_s_5683_, 2);
lean_inc(v_pos_5685_);
v_inputString_5686_ = lean_ctor_get(v_toInputContext_5684_, 0);
v___f_5687_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_initStackSz_5688_ = l_Lean_Parser_ParserState_stackSize(v_s_5683_);
v_curr_5693_ = lean_string_utf8_get(v_inputString_5686_, v_pos_5685_);
v___x_5701_ = 48;
v___x_5702_ = lean_uint32_dec_le(v___x_5701_, v_curr_5693_);
if (v___x_5702_ == 0)
{
v___y_5695_ = v___x_5702_;
goto v___jp_5694_;
}
else
{
uint32_t v___x_5703_; uint8_t v___x_5704_; 
v___x_5703_ = 57;
v___x_5704_ = lean_uint32_dec_le(v_curr_5693_, v___x_5703_);
v___y_5695_ = v___x_5704_;
goto v___jp_5694_;
}
v___jp_5689_:
{
lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5690_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5691_, 0, v_initStackSz_5688_);
v___x_5692_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5683_, v___x_5690_, v_pos_5685_, v___x_5691_);
lean_dec_ref_known(v___x_5691_, 1);
return v___x_5692_;
}
v___jp_5694_:
{
if (v___y_5695_ == 0)
{
lean_dec_ref(v_c_5682_);
goto v___jp_5689_;
}
else
{
uint32_t v___x_5696_; uint8_t v___x_5697_; 
v___x_5696_ = 48;
v___x_5697_ = lean_uint32_dec_eq(v_curr_5693_, v___x_5696_);
if (v___x_5697_ == 0)
{
lean_object* v_s_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
lean_dec(v_initStackSz_5688_);
v_s_5698_ = l_Lean_Parser_takeWhileFn(v___f_5687_, v_c_5682_, v_s_5683_);
v___x_5699_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5700_ = l_Lean_Parser_mkNodeToken(v___x_5699_, v_pos_5685_, v___y_5695_, v_c_5682_, v_s_5698_);
return v___x_5700_;
}
else
{
lean_dec_ref(v_c_5682_);
goto v___jp_5689_;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5705_; uint8_t v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; 
v___x_5705_ = 0;
v___x_5706_ = 1;
v___x_5707_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5708_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5709_ = l_Lean_Parser_mkAntiquot(v___x_5708_, v___x_5707_, v___x_5706_, v___x_5705_);
return v___x_5709_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; 
v___x_5710_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5711_ = l_Lean_Parser_mkAtomicInfo(v___x_5710_);
return v___x_5711_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
v___x_5712_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5713_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5713_);
lean_ctor_set(v___x_5714_, 1, v___x_5712_);
return v___x_5714_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; 
v___x_5715_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5716_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5717_ = l_Lean_Parser_withAntiquot(v___x_5716_, v___x_5715_);
return v___x_5717_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5718_; 
v___x_5718_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5719_, lean_object* v_s_5720_){
_start:
{
lean_inc_ref(v_s_5720_);
return v_s_5720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5721_, lean_object* v_s_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l_Lean_Parser_skip___lam__0(v_x_5721_, v_s_5722_);
lean_dec_ref(v_s_5722_);
lean_dec_ref(v_x_5721_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5729_, lean_object* v_s_5730_, lean_object* v_f_5731_, lean_object* v_b_5732_){
_start:
{
lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; uint8_t v___x_5736_; 
v___x_5733_ = l_Lean_Syntax_getArgs(v_s_5730_);
v___x_5734_ = lean_unsigned_to_nat(0u);
v___x_5735_ = lean_array_get_size(v___x_5733_);
v___x_5736_ = lean_nat_dec_lt(v___x_5734_, v___x_5735_);
if (v___x_5736_ == 0)
{
lean_object* v_toApplicative_5737_; lean_object* v_toPure_5738_; lean_object* v___x_5739_; 
lean_dec_ref(v___x_5733_);
lean_dec(v_f_5731_);
v_toApplicative_5737_ = lean_ctor_get(v_inst_5729_, 0);
lean_inc_ref(v_toApplicative_5737_);
lean_dec_ref(v_inst_5729_);
v_toPure_5738_ = lean_ctor_get(v_toApplicative_5737_, 1);
lean_inc(v_toPure_5738_);
lean_dec_ref(v_toApplicative_5737_);
v___x_5739_ = lean_apply_2(v_toPure_5738_, lean_box(0), v_b_5732_);
return v___x_5739_;
}
else
{
lean_object* v___x_5740_; uint8_t v___x_5741_; 
v___x_5740_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5740_, 0, lean_box(0));
lean_closure_set(v___x_5740_, 1, lean_box(0));
lean_closure_set(v___x_5740_, 2, lean_box(0));
lean_closure_set(v___x_5740_, 3, v_f_5731_);
v___x_5741_ = lean_nat_dec_le(v___x_5735_, v___x_5735_);
if (v___x_5741_ == 0)
{
if (v___x_5736_ == 0)
{
lean_object* v_toApplicative_5742_; lean_object* v_toPure_5743_; lean_object* v___x_5744_; 
lean_dec_ref(v___x_5740_);
lean_dec_ref(v___x_5733_);
v_toApplicative_5742_ = lean_ctor_get(v_inst_5729_, 0);
lean_inc_ref(v_toApplicative_5742_);
lean_dec_ref(v_inst_5729_);
v_toPure_5743_ = lean_ctor_get(v_toApplicative_5742_, 1);
lean_inc(v_toPure_5743_);
lean_dec_ref(v_toApplicative_5742_);
v___x_5744_ = lean_apply_2(v_toPure_5743_, lean_box(0), v_b_5732_);
return v___x_5744_;
}
else
{
size_t v___x_5745_; size_t v___x_5746_; lean_object* v___x_5747_; 
v___x_5745_ = ((size_t)0ULL);
v___x_5746_ = lean_usize_of_nat(v___x_5735_);
v___x_5747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5729_, v___x_5740_, v___x_5733_, v___x_5745_, v___x_5746_, v_b_5732_);
return v___x_5747_;
}
}
else
{
size_t v___x_5748_; size_t v___x_5749_; lean_object* v___x_5750_; 
v___x_5748_ = ((size_t)0ULL);
v___x_5749_ = lean_usize_of_nat(v___x_5735_);
v___x_5750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5729_, v___x_5740_, v___x_5733_, v___x_5748_, v___x_5749_, v_b_5732_);
return v___x_5750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5751_, lean_object* v_s_5752_, lean_object* v_f_5753_, lean_object* v_b_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5751_, v_s_5752_, v_f_5753_, v_b_5754_);
lean_dec(v_s_5752_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5756_, lean_object* v_inst_5757_, lean_object* v_00_u03b2_5758_, lean_object* v_s_5759_, lean_object* v_f_5760_, lean_object* v_b_5761_){
_start:
{
lean_object* v___x_5762_; 
v___x_5762_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5757_, v_s_5759_, v_f_5760_, v_b_5761_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5763_, lean_object* v_inst_5764_, lean_object* v_00_u03b2_5765_, lean_object* v_s_5766_, lean_object* v_f_5767_, lean_object* v_b_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Lean_Syntax_foldArgsM(v_m_5763_, v_inst_5764_, v_00_u03b2_5765_, v_s_5766_, v_f_5767_, v_b_5768_);
lean_dec(v_s_5766_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5770_, lean_object* v_x1_5771_, lean_object* v_x2_5772_){
_start:
{
lean_object* v___x_5773_; 
v___x_5773_ = lean_apply_2(v_f_5770_, v_x1_5771_, v_x2_5772_);
return v___x_5773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5774_, lean_object* v_as_5775_, size_t v_i_5776_, size_t v_stop_5777_, lean_object* v_b_5778_){
_start:
{
uint8_t v___x_5779_; 
v___x_5779_ = lean_usize_dec_eq(v_i_5776_, v_stop_5777_);
if (v___x_5779_ == 0)
{
lean_object* v___x_5780_; lean_object* v___x_5781_; size_t v___x_5782_; size_t v___x_5783_; 
v___x_5780_ = lean_array_uget_borrowed(v_as_5775_, v_i_5776_);
lean_inc(v_f_5774_);
lean_inc(v___x_5780_);
v___x_5781_ = lean_apply_2(v_f_5774_, v___x_5780_, v_b_5778_);
v___x_5782_ = ((size_t)1ULL);
v___x_5783_ = lean_usize_add(v_i_5776_, v___x_5782_);
v_i_5776_ = v___x_5783_;
v_b_5778_ = v___x_5781_;
goto _start;
}
else
{
lean_dec(v_f_5774_);
return v_b_5778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5785_, lean_object* v_as_5786_, lean_object* v_i_5787_, lean_object* v_stop_5788_, lean_object* v_b_5789_){
_start:
{
size_t v_i_boxed_5790_; size_t v_stop_boxed_5791_; lean_object* v_res_5792_; 
v_i_boxed_5790_ = lean_unbox_usize(v_i_5787_);
lean_dec(v_i_5787_);
v_stop_boxed_5791_ = lean_unbox_usize(v_stop_5788_);
lean_dec(v_stop_5788_);
v_res_5792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5785_, v_as_5786_, v_i_boxed_5790_, v_stop_boxed_5791_, v_b_5789_);
lean_dec_ref(v_as_5786_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5793_, lean_object* v_f_5794_, lean_object* v_b_5795_){
_start:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; uint8_t v___x_5799_; 
v___x_5796_ = l_Lean_Syntax_getArgs(v_s_5793_);
v___x_5797_ = lean_unsigned_to_nat(0u);
v___x_5798_ = lean_array_get_size(v___x_5796_);
v___x_5799_ = lean_nat_dec_lt(v___x_5797_, v___x_5798_);
if (v___x_5799_ == 0)
{
lean_dec_ref(v___x_5796_);
lean_dec(v_f_5794_);
return v_b_5795_;
}
else
{
uint8_t v___x_5800_; 
v___x_5800_ = lean_nat_dec_le(v___x_5798_, v___x_5798_);
if (v___x_5800_ == 0)
{
if (v___x_5799_ == 0)
{
lean_dec_ref(v___x_5796_);
lean_dec(v_f_5794_);
return v_b_5795_;
}
else
{
size_t v___x_5801_; size_t v___x_5802_; lean_object* v___x_5803_; 
v___x_5801_ = ((size_t)0ULL);
v___x_5802_ = lean_usize_of_nat(v___x_5798_);
v___x_5803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5794_, v___x_5796_, v___x_5801_, v___x_5802_, v_b_5795_);
lean_dec_ref(v___x_5796_);
return v___x_5803_;
}
}
else
{
size_t v___x_5804_; size_t v___x_5805_; lean_object* v___x_5806_; 
v___x_5804_ = ((size_t)0ULL);
v___x_5805_ = lean_usize_of_nat(v___x_5798_);
v___x_5806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5794_, v___x_5796_, v___x_5804_, v___x_5805_, v_b_5795_);
lean_dec_ref(v___x_5796_);
return v___x_5806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5807_, lean_object* v_f_5808_, lean_object* v_b_5809_){
_start:
{
lean_object* v_res_5810_; 
v_res_5810_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5807_, v_f_5808_, v_b_5809_);
lean_dec(v_s_5807_);
return v_res_5810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5811_, lean_object* v_f_5812_, lean_object* v_b_5813_){
_start:
{
lean_object* v___f_5814_; lean_object* v___x_5815_; 
v___f_5814_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5814_, 0, v_f_5812_);
v___x_5815_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5811_, v___f_5814_, v_b_5813_);
return v___x_5815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_5816_, lean_object* v_f_5817_, lean_object* v_b_5818_){
_start:
{
lean_object* v_res_5819_; 
v_res_5819_ = l_Lean_Syntax_foldArgs___redArg(v_s_5816_, v_f_5817_, v_b_5818_);
lean_dec(v_s_5816_);
return v_res_5819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_5820_, lean_object* v_s_5821_, lean_object* v_f_5822_, lean_object* v_b_5823_){
_start:
{
lean_object* v___x_5824_; 
v___x_5824_ = l_Lean_Syntax_foldArgs___redArg(v_s_5821_, v_f_5822_, v_b_5823_);
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_5825_, lean_object* v_s_5826_, lean_object* v_f_5827_, lean_object* v_b_5828_){
_start:
{
lean_object* v_res_5829_; 
v_res_5829_ = l_Lean_Syntax_foldArgs(v_00_u03b2_5825_, v_s_5826_, v_f_5827_, v_b_5828_);
lean_dec(v_s_5826_);
return v_res_5829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_5830_, lean_object* v_s_5831_, lean_object* v_f_5832_, lean_object* v_b_5833_){
_start:
{
lean_object* v___x_5834_; 
v___x_5834_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5831_, v_f_5832_, v_b_5833_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_5835_, lean_object* v_s_5836_, lean_object* v_f_5837_, lean_object* v_b_5838_){
_start:
{
lean_object* v_res_5839_; 
v_res_5839_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_5835_, v_s_5836_, v_f_5837_, v_b_5838_);
lean_dec(v_s_5836_);
return v_res_5839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_5840_, lean_object* v_f_5841_, lean_object* v_as_5842_, size_t v_i_5843_, size_t v_stop_5844_, lean_object* v_b_5845_){
_start:
{
lean_object* v___x_5846_; 
v___x_5846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5841_, v_as_5842_, v_i_5843_, v_stop_5844_, v_b_5845_);
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5847_, lean_object* v_f_5848_, lean_object* v_as_5849_, lean_object* v_i_5850_, lean_object* v_stop_5851_, lean_object* v_b_5852_){
_start:
{
size_t v_i_boxed_5853_; size_t v_stop_boxed_5854_; lean_object* v_res_5855_; 
v_i_boxed_5853_ = lean_unbox_usize(v_i_5850_);
lean_dec(v_i_5850_);
v_stop_boxed_5854_ = lean_unbox_usize(v_stop_5851_);
lean_dec(v_stop_5851_);
v_res_5855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_5847_, v_f_5848_, v_as_5849_, v_i_boxed_5853_, v_stop_boxed_5854_, v_b_5852_);
lean_dec_ref(v_as_5849_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_5856_, lean_object* v_s_5857_, lean_object* v_x_5858_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = lean_apply_1(v_f_5856_, v_s_5857_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_5860_, lean_object* v_s_5861_, lean_object* v_f_5862_){
_start:
{
lean_object* v___f_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___f_5863_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5863_, 0, v_f_5862_);
v___x_5864_ = lean_box(0);
v___x_5865_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5860_, v_s_5861_, v___f_5863_, v___x_5864_);
return v___x_5865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_5866_, lean_object* v_s_5867_, lean_object* v_f_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l_Lean_Syntax_forArgsM___redArg(v_inst_5866_, v_s_5867_, v_f_5868_);
lean_dec(v_s_5867_);
return v_res_5869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_5870_, lean_object* v_inst_5871_, lean_object* v_s_5872_, lean_object* v_f_5873_){
_start:
{
lean_object* v___x_5874_; 
v___x_5874_ = l_Lean_Syntax_forArgsM___redArg(v_inst_5871_, v_s_5872_, v_f_5873_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_5875_, lean_object* v_inst_5876_, lean_object* v_s_5877_, lean_object* v_f_5878_){
_start:
{
lean_object* v_res_5879_; 
v_res_5879_ = l_Lean_Syntax_forArgsM(v_m_5875_, v_inst_5876_, v_s_5877_, v_f_5878_);
lean_dec(v_s_5877_);
return v_res_5879_;
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
