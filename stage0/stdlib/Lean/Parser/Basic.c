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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
lean_dec_ref_known(v_x_146_, 1);
v___x_148_ = 0;
return v___x_148_;
}
}
else
{
if (lean_obj_tag(v_x_146_) == 0)
{
uint8_t v___x_149_; 
lean_dec_ref_known(v_x_145_, 1);
v___x_149_ = 0;
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v_val_151_; uint8_t v___x_152_; 
v_val_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v_x_145_, 1);
v_val_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v_x_146_, 1);
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
lean_object* v_s_161_; lean_object* v_errorMsg_162_; lean_object* v___x_163_; uint8_t v___x_164_; uint8_t v___x_165_; 
lean_inc_ref(v_c_159_);
v_s_161_ = lean_apply_2(v_p_157_, v_c_159_, v_s_160_);
v_errorMsg_162_ = lean_ctor_get(v_s_161_, 4);
lean_inc(v_errorMsg_162_);
v___x_163_ = lean_box(0);
v___x_164_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_162_, v___x_163_);
v___x_165_ = lean_bool_not(v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_apply_2(v_q_158_, v_c_159_, v_s_161_);
return v___x_166_;
}
else
{
lean_dec_ref(v_c_159_);
lean_dec_ref(v_q_158_);
return v_s_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__0(lean_object* v_collectKinds_167_, lean_object* v_collectKinds_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_apply_1(v_collectKinds_167_, v___y_169_);
v___x_171_ = lean_apply_1(v_collectKinds_168_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__1(lean_object* v_collectTokens_172_, lean_object* v_collectTokens_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_apply_1(v_collectTokens_172_, v___y_174_);
v___x_176_ = lean_apply_1(v_collectTokens_173_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object* v_p_177_, lean_object* v_q_178_){
_start:
{
lean_object* v_collectTokens_179_; lean_object* v_collectKinds_180_; lean_object* v_firstTokens_181_; lean_object* v_collectTokens_182_; lean_object* v_collectKinds_183_; lean_object* v_firstTokens_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_194_; 
v_collectTokens_179_ = lean_ctor_get(v_p_177_, 0);
lean_inc_ref(v_collectTokens_179_);
v_collectKinds_180_ = lean_ctor_get(v_p_177_, 1);
lean_inc_ref(v_collectKinds_180_);
v_firstTokens_181_ = lean_ctor_get(v_p_177_, 2);
lean_inc(v_firstTokens_181_);
lean_dec_ref(v_p_177_);
v_collectTokens_182_ = lean_ctor_get(v_q_178_, 0);
v_collectKinds_183_ = lean_ctor_get(v_q_178_, 1);
v_firstTokens_184_ = lean_ctor_get(v_q_178_, 2);
v_isSharedCheck_194_ = !lean_is_exclusive(v_q_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_186_ = v_q_178_;
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_firstTokens_184_);
lean_inc(v_collectKinds_183_);
lean_inc(v_collectTokens_182_);
lean_dec(v_q_178_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___f_188_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_188_, 0, v_collectKinds_183_);
lean_closure_set(v___f_188_, 1, v_collectKinds_180_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_189_, 0, v_collectTokens_182_);
lean_closure_set(v___f_189_, 1, v_collectTokens_179_);
v___x_190_ = l_Lean_Parser_FirstTokens_seq(v_firstTokens_181_, v_firstTokens_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 2, v___x_190_);
lean_ctor_set(v___x_186_, 1, v___f_188_);
lean_ctor_set(v___x_186_, 0, v___f_189_);
v___x_192_ = v___x_186_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___f_189_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___f_188_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParserFn___lam__0(lean_object* v_p1_195_, lean_object* v_p2_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_p2_196_, v___x_199_);
v___x_201_ = l_Lean_Parser_andthenFn(v_p1_195_, v___x_200_, v___y_197_, v___y_198_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object* v_p_204_, lean_object* v_q_205_){
_start:
{
lean_object* v_info_206_; lean_object* v_fn_207_; lean_object* v_info_208_; lean_object* v_fn_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_218_; 
v_info_206_ = lean_ctor_get(v_p_204_, 0);
lean_inc_ref(v_info_206_);
v_fn_207_ = lean_ctor_get(v_p_204_, 1);
lean_inc_ref(v_fn_207_);
lean_dec_ref(v_p_204_);
v_info_208_ = lean_ctor_get(v_q_205_, 0);
v_fn_209_ = lean_ctor_get(v_q_205_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_q_205_);
if (v_isSharedCheck_218_ == 0)
{
v___x_211_ = v_q_205_;
v_isShared_212_ = v_isSharedCheck_218_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_fn_209_);
lean_inc(v_info_208_);
lean_dec(v_q_205_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_218_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_213_ = l_Lean_Parser_andthenInfo(v_info_206_, v_info_208_);
v___x_214_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_214_, 0, v_fn_207_);
lean_closure_set(v___x_214_, 1, v_fn_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_214_);
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_216_ = v___x_211_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser___lam__0(lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v_b_220_, v___x_221_);
v___x_223_ = l_Lean_Parser_andthen(v_a_219_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object* v_n_226_, lean_object* v_p_227_, lean_object* v_c_228_, lean_object* v_s_229_){
_start:
{
lean_object* v_iniSz_230_; lean_object* v_s_231_; lean_object* v___x_232_; 
v_iniSz_230_ = l_Lean_Parser_ParserState_stackSize(v_s_229_);
v_s_231_ = lean_apply_2(v_p_227_, v_c_228_, v_s_229_);
v___x_232_ = l_Lean_Parser_ParserState_mkNode(v_s_231_, v_n_226_, v_iniSz_230_);
lean_dec(v_iniSz_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object* v_n_233_, lean_object* v_p_234_, lean_object* v_c_235_, lean_object* v_s_236_){
_start:
{
lean_object* v_iniSz_237_; lean_object* v_s_238_; lean_object* v___x_239_; 
v_iniSz_237_ = l_Lean_Parser_ParserState_stackSize(v_s_236_);
v_s_238_ = lean_apply_2(v_p_234_, v_c_235_, v_s_236_);
v___x_239_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_238_, v_n_233_, v_iniSz_237_);
lean_dec(v_iniSz_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___lam__0(lean_object* v_collectKinds_240_, lean_object* v_n_241_, lean_object* v_s_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_apply_1(v_collectKinds_240_, v_s_242_);
v___x_244_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v___x_243_, v_n_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object* v_n_245_, lean_object* v_p_246_){
_start:
{
lean_object* v_collectTokens_247_; lean_object* v_collectKinds_248_; lean_object* v_firstTokens_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_257_; 
v_collectTokens_247_ = lean_ctor_get(v_p_246_, 0);
v_collectKinds_248_ = lean_ctor_get(v_p_246_, 1);
v_firstTokens_249_ = lean_ctor_get(v_p_246_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_p_246_);
if (v_isSharedCheck_257_ == 0)
{
v___x_251_ = v_p_246_;
v_isShared_252_ = v_isSharedCheck_257_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_firstTokens_249_);
lean_inc(v_collectKinds_248_);
lean_inc(v_collectTokens_247_);
lean_dec(v_p_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_257_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___f_253_; lean_object* v___x_255_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___lam__0), 3, 2);
lean_closure_set(v___f_253_, 0, v_collectKinds_248_);
lean_closure_set(v___f_253_, 1, v_n_245_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___f_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_collectTokens_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___f_253_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_firstTokens_249_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object* v_n_258_, lean_object* v_p_259_){
_start:
{
lean_object* v_info_260_; lean_object* v_fn_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_270_; 
v_info_260_ = lean_ctor_get(v_p_259_, 0);
v_fn_261_ = lean_ctor_get(v_p_259_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_p_259_);
if (v_isSharedCheck_270_ == 0)
{
v___x_263_ = v_p_259_;
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_fn_261_);
lean_inc(v_info_260_);
lean_dec(v_p_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_n_258_);
v___x_265_ = l_Lean_Parser_nodeInfo(v_n_258_, v_info_260_);
v___x_266_ = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(v___x_266_, 0, v_n_258_);
lean_closure_set(v___x_266_, 1, v_fn_261_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_266_);
lean_ctor_set(v___x_263_, 0, v___x_265_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___redArg(lean_object* v_msg_271_, lean_object* v_s_272_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = 1;
v___x_275_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_272_, v_msg_271_, v___x_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object* v_msg_276_, lean_object* v_x_277_, lean_object* v_s_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Parser_errorFn___redArg(v_msg_276_, v_s_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object* v_msg_280_, lean_object* v_x_281_, lean_object* v_s_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Parser_errorFn(v_msg_280_, v_x_281_, v_s_282_);
lean_dec_ref(v_x_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object* v_msg_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_286_ = lean_alloc_closure((void*)(l_Lean_Parser_errorFn___boxed), 3, 1);
lean_closure_set(v___x_286_, 0, v_msg_284_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* v_msg_288_, uint8_t v_delta_289_, lean_object* v_c_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_toCacheableParserContext_292_; lean_object* v_savedPos_x3f_293_; 
v_toCacheableParserContext_292_ = lean_ctor_get(v_c_290_, 2);
v_savedPos_x3f_293_ = lean_ctor_get(v_toCacheableParserContext_292_, 2);
lean_inc(v_savedPos_x3f_293_);
if (lean_obj_tag(v_savedPos_x3f_293_) == 0)
{
lean_dec_ref(v_c_290_);
lean_dec_ref(v_msg_288_);
return v_s_291_;
}
else
{
if (v_delta_289_ == 0)
{
lean_object* v_val_294_; lean_object* v___x_295_; 
lean_dec_ref(v_c_290_);
v_val_294_ = lean_ctor_get(v_savedPos_x3f_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v_savedPos_x3f_293_, 1);
v___x_295_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_291_, v_msg_288_, v_val_294_);
return v___x_295_;
}
else
{
lean_object* v_toInputContext_296_; lean_object* v_val_297_; lean_object* v_inputString_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_toInputContext_296_ = lean_ctor_get(v_c_290_, 0);
lean_inc_ref(v_toInputContext_296_);
lean_dec_ref(v_c_290_);
v_val_297_ = lean_ctor_get(v_savedPos_x3f_293_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v_savedPos_x3f_293_, 1);
v_inputString_298_ = lean_ctor_get(v_toInputContext_296_, 0);
lean_inc_ref(v_inputString_298_);
lean_dec_ref(v_toInputContext_296_);
v___x_299_ = lean_string_utf8_next(v_inputString_298_, v_val_297_);
lean_dec(v_val_297_);
lean_dec_ref(v_inputString_298_);
v___x_300_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_291_, v_msg_288_, v___x_299_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object* v_msg_301_, lean_object* v_delta_302_, lean_object* v_c_303_, lean_object* v_s_304_){
_start:
{
uint8_t v_delta_boxed_305_; lean_object* v_res_306_; 
v_delta_boxed_305_ = lean_unbox(v_delta_302_);
v_res_306_ = l_Lean_Parser_errorAtSavedPosFn(v_msg_301_, v_delta_boxed_305_, v_c_303_, v_s_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object* v_msg_311_, uint8_t v_delta_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_314_ = lean_box(v_delta_312_);
v___x_315_ = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn___boxed), 4, 2);
lean_closure_set(v___x_315_, 0, v_msg_311_);
lean_closure_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_313_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object* v_msg_317_, lean_object* v_delta_318_){
_start:
{
uint8_t v_delta_boxed_319_; lean_object* v_res_320_; 
v_delta_boxed_319_ = lean_unbox(v_delta_318_);
v_res_320_ = l_Lean_Parser_errorAtSavedPos(v_msg_317_, v_delta_boxed_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3));
v___x_331_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4));
v___x_332_ = l_Lean_addBuiltinDocString(v___x_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___boxed(lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object* v_prec_336_, lean_object* v_c_337_, lean_object* v_s_338_){
_start:
{
lean_object* v_toCacheableParserContext_339_; lean_object* v_prec_340_; uint8_t v___x_341_; 
v_toCacheableParserContext_339_ = lean_ctor_get(v_c_337_, 2);
v_prec_340_ = lean_ctor_get(v_toCacheableParserContext_339_, 0);
v___x_341_ = lean_nat_dec_le(v_prec_340_, v_prec_336_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_342_ = ((lean_object*)(l_Lean_Parser_checkPrecFn___closed__0));
v___x_343_ = lean_box(0);
v___x_344_ = 1;
v___x_345_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_338_, v___x_342_, v___x_343_, v___x_344_);
return v___x_345_;
}
else
{
return v_s_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object* v_prec_346_, lean_object* v_c_347_, lean_object* v_s_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Parser_checkPrecFn(v_prec_346_, v_c_347_, v_s_348_);
lean_dec_ref(v_c_347_);
lean_dec(v_prec_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object* v_prec_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_352_ = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(v___x_352_, 0, v_prec_350_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg(lean_object* v_prec_354_, lean_object* v_s_355_){
_start:
{
lean_object* v_lhsPrec_356_; uint8_t v___x_357_; 
v_lhsPrec_356_ = lean_ctor_get(v_s_355_, 1);
v___x_357_ = lean_nat_dec_le(v_prec_354_, v_lhsPrec_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; 
v___x_358_ = ((lean_object*)(l_Lean_Parser_checkPrecFn___closed__0));
v___x_359_ = lean_box(0);
v___x_360_ = 1;
v___x_361_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_355_, v___x_358_, v___x_359_, v___x_360_);
return v___x_361_;
}
else
{
return v_s_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg___boxed(lean_object* v_prec_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Parser_checkLhsPrecFn___redArg(v_prec_362_, v_s_363_);
lean_dec(v_prec_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object* v_prec_365_, lean_object* v_x_366_, lean_object* v_s_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Parser_checkLhsPrecFn___redArg(v_prec_365_, v_s_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object* v_prec_369_, lean_object* v_x_370_, lean_object* v_s_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Parser_checkLhsPrecFn(v_prec_369_, v_x_370_, v_s_371_);
lean_dec_ref(v_x_370_);
lean_dec(v_prec_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object* v_prec_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_375_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(v___x_375_, 0, v_prec_373_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___redArg(lean_object* v_prec_377_, lean_object* v_s_378_){
_start:
{
lean_object* v_stxStack_379_; lean_object* v_pos_380_; lean_object* v_cache_381_; lean_object* v_errorMsg_382_; lean_object* v_recoveredErrors_383_; lean_object* v___x_384_; uint8_t v___x_385_; uint8_t v___x_386_; 
v_stxStack_379_ = lean_ctor_get(v_s_378_, 0);
v_pos_380_ = lean_ctor_get(v_s_378_, 2);
v_cache_381_ = lean_ctor_get(v_s_378_, 3);
v_errorMsg_382_ = lean_ctor_get(v_s_378_, 4);
v_recoveredErrors_383_ = lean_ctor_get(v_s_378_, 5);
v___x_384_ = lean_box(0);
lean_inc(v_errorMsg_382_);
v___x_385_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_382_, v___x_384_);
v___x_386_ = lean_bool_not(v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_inc_ref(v_recoveredErrors_383_);
lean_inc(v_errorMsg_382_);
lean_inc_ref(v_cache_381_);
lean_inc(v_pos_380_);
lean_inc_ref(v_stxStack_379_);
v_isSharedCheck_393_ = !lean_is_exclusive(v_s_378_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_394_ = lean_ctor_get(v_s_378_, 5);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_s_378_, 4);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_s_378_, 3);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_s_378_, 2);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_s_378_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_s_378_, 0);
lean_dec(v_unused_399_);
v___x_388_ = v_s_378_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_s_378_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_prec_377_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_stxStack_379_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_prec_377_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_pos_380_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_cache_381_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_errorMsg_382_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v_recoveredErrors_383_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_dec(v_prec_377_);
return v_s_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object* v_prec_400_, lean_object* v_x_401_, lean_object* v_s_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Parser_setLhsPrecFn___redArg(v_prec_400_, v_s_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object* v_prec_404_, lean_object* v_x_405_, lean_object* v_s_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Parser_setLhsPrecFn(v_prec_404_, v_x_405_, v_s_406_);
lean_dec_ref(v_x_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object* v_prec_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_410_ = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(v___x_410_, 0, v_prec_408_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_spec__0(lean_object* v_a_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_nat_to_int(v_a_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(lean_object* v_i_414_, lean_object* v_c_415_){
_start:
{
lean_object* v_prec_416_; lean_object* v_quotDepth_417_; uint8_t v_suppressInsideQuot_418_; lean_object* v_savedPos_x3f_419_; lean_object* v_forbiddenTk_x3f_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
v_prec_416_ = lean_ctor_get(v_c_415_, 0);
v_quotDepth_417_ = lean_ctor_get(v_c_415_, 1);
v_suppressInsideQuot_418_ = lean_ctor_get_uint8(v_c_415_, sizeof(void*)*4);
v_savedPos_x3f_419_ = lean_ctor_get(v_c_415_, 2);
v_forbiddenTk_x3f_420_ = lean_ctor_get(v_c_415_, 3);
v_isSharedCheck_430_ = !lean_is_exclusive(v_c_415_);
if (v_isSharedCheck_430_ == 0)
{
v___x_422_ = v_c_415_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_forbiddenTk_x3f_420_);
lean_inc(v_savedPos_x3f_419_);
lean_inc(v_quotDepth_417_);
lean_inc(v_prec_416_);
lean_dec(v_c_415_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_424_ = lean_nat_to_int(v_quotDepth_417_);
v___x_425_ = lean_int_add(v___x_424_, v_i_414_);
lean_dec(v___x_424_);
v___x_426_ = l_Int_toNat(v___x_425_);
lean_dec(v___x_425_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v___x_426_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_prec_416_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_savedPos_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_forbiddenTk_x3f_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*4, v_suppressInsideQuot_418_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed(lean_object* v_i_431_, lean_object* v_c_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(v_i_431_, v_c_432_);
lean_dec(v_i_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object* v_i_434_, lean_object* v_p_435_){
_start:
{
lean_object* v___f_436_; lean_object* v___x_437_; 
v___f_436_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed), 2, 1);
lean_closure_set(v___f_436_, 0, v_i_434_);
v___x_437_ = l_Lean_Parser_adaptCacheableContext(v___f_436_, v_p_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Parser_incQuotDepth___closed__0(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_to_int(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object* v_p_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___x_442_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(v___x_441_, v_p_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Parser_decQuotDepth___closed__0(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___x_444_ = lean_int_neg(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object* v_p_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_Parser_decQuotDepth___closed__0, &l_Lean_Parser_decQuotDepth___closed__0_once, _init_l_Lean_Parser_decQuotDepth___closed__0);
v___x_447_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(v___x_446_, v_p_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0(lean_object* v_c_448_){
_start:
{
lean_object* v_prec_449_; lean_object* v_quotDepth_450_; lean_object* v_savedPos_x3f_451_; lean_object* v_forbiddenTk_x3f_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_prec_449_ = lean_ctor_get(v_c_448_, 0);
v_quotDepth_450_ = lean_ctor_get(v_c_448_, 1);
v_savedPos_x3f_451_ = lean_ctor_get(v_c_448_, 2);
v_forbiddenTk_x3f_452_ = lean_ctor_get(v_c_448_, 3);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_nat_dec_eq(v_quotDepth_450_, v___x_453_);
if (v___x_454_ == 0)
{
return v_c_448_;
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_inc(v_forbiddenTk_x3f_452_);
lean_inc(v_savedPos_x3f_451_);
lean_inc(v_quotDepth_450_);
lean_inc(v_prec_449_);
v_isSharedCheck_461_ = !lean_is_exclusive(v_c_448_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; 
v_unused_462_ = lean_ctor_get(v_c_448_, 3);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_c_448_, 2);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_c_448_, 1);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_c_448_, 0);
lean_dec(v_unused_465_);
v___x_456_ = v_c_448_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_c_448_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_prec_449_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_quotDepth_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_savedPos_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_forbiddenTk_x3f_452_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*4, v___x_454_);
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* v_a_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; 
v___f_468_ = ((lean_object*)(l_Lean_Parser_suppressInsideQuot___closed__0));
v___x_469_ = l_Lean_Parser_adaptCacheableContext(v___f_468_, v_a_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object* v_n_470_, lean_object* v_prec_471_, lean_object* v_p_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_inc(v_prec_471_);
v___x_473_ = l_Lean_Parser_checkPrec(v_prec_471_);
v___x_474_ = l_Lean_Parser_node(v_n_470_, v_p_472_);
v___x_475_ = l_Lean_Parser_setLhsPrec(v_prec_471_);
v___x_476_ = l_Lean_Parser_andthen(v___x_474_, v___x_475_);
v___x_477_ = l_Lean_Parser_andthen(v___x_473_, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object* v_n_478_, lean_object* v_p_479_){
_start:
{
lean_object* v_info_480_; lean_object* v_fn_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
v_info_480_ = lean_ctor_get(v_p_479_, 0);
v_fn_481_ = lean_ctor_get(v_p_479_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_p_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v_p_479_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_fn_481_);
lean_inc(v_info_480_);
lean_dec(v_p_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
lean_inc(v_n_478_);
v___x_485_ = l_Lean_Parser_nodeInfo(v_n_478_, v_info_480_);
v___x_486_ = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(v___x_486_, 0, v_n_478_);
lean_closure_set(v___x_486_, 1, v_fn_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_486_);
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object* v_n_491_, lean_object* v_prec_492_, lean_object* v_lhsPrec_493_, lean_object* v_p_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_inc(v_prec_492_);
v___x_495_ = l_Lean_Parser_checkPrec(v_prec_492_);
v___x_496_ = l_Lean_Parser_checkLhsPrec(v_lhsPrec_493_);
v___x_497_ = l_Lean_Parser_trailingNodeAux(v_n_491_, v_p_494_);
v___x_498_ = l_Lean_Parser_setLhsPrec(v_prec_492_);
v___x_499_ = l_Lean_Parser_andthen(v___x_497_, v___x_498_);
v___x_500_ = l_Lean_Parser_andthen(v___x_496_, v___x_499_);
v___x_501_ = l_Lean_Parser_andthen(v___x_495_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* v_s_502_, lean_object* v_error1_503_, lean_object* v_iniPos_504_, uint8_t v_mergeErrors_505_){
_start:
{
lean_object* v_stxStack_506_; lean_object* v_lhsPrec_507_; lean_object* v_pos_508_; lean_object* v_cache_509_; lean_object* v_errorMsg_510_; lean_object* v_recoveredErrors_511_; lean_object* v___y_513_; 
v_stxStack_506_ = lean_ctor_get(v_s_502_, 0);
v_lhsPrec_507_ = lean_ctor_get(v_s_502_, 1);
v_pos_508_ = lean_ctor_get(v_s_502_, 2);
v_cache_509_ = lean_ctor_get(v_s_502_, 3);
v_errorMsg_510_ = lean_ctor_get(v_s_502_, 4);
v_recoveredErrors_511_ = lean_ctor_get(v_s_502_, 5);
if (lean_obj_tag(v_errorMsg_510_) == 1)
{
lean_object* v_val_516_; uint8_t v___x_517_; 
v_val_516_ = lean_ctor_get(v_errorMsg_510_, 0);
v___x_517_ = lean_nat_dec_eq(v_pos_508_, v_iniPos_504_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_error1_503_);
return v_s_502_;
}
else
{
lean_inc(v_val_516_);
lean_inc_ref(v_recoveredErrors_511_);
lean_inc_ref(v_cache_509_);
lean_inc(v_pos_508_);
lean_inc(v_lhsPrec_507_);
lean_inc_ref(v_stxStack_506_);
lean_dec_ref(v_s_502_);
if (v_mergeErrors_505_ == 0)
{
lean_dec_ref(v_error1_503_);
v___y_513_ = v_val_516_;
goto v___jp_512_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Parser_Error_merge(v_error1_503_, v_val_516_);
v___y_513_ = v___x_518_;
goto v___jp_512_;
}
}
}
else
{
lean_dec_ref(v_error1_503_);
return v_s_502_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___y_513_);
v___x_515_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_515_, 0, v_stxStack_506_);
lean_ctor_set(v___x_515_, 1, v_lhsPrec_507_);
lean_ctor_set(v___x_515_, 2, v_pos_508_);
lean_ctor_set(v___x_515_, 3, v_cache_509_);
lean_ctor_set(v___x_515_, 4, v___x_514_);
lean_ctor_set(v___x_515_, 5, v_recoveredErrors_511_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* v_s_519_, lean_object* v_error1_520_, lean_object* v_iniPos_521_, lean_object* v_mergeErrors_522_){
_start:
{
uint8_t v_mergeErrors_boxed_523_; lean_object* v_res_524_; 
v_mergeErrors_boxed_523_ = lean_unbox(v_mergeErrors_522_);
v_res_524_ = l_Lean_Parser_mergeOrElseErrors(v_s_519_, v_error1_520_, v_iniPos_521_, v_mergeErrors_boxed_523_);
lean_dec(v_iniPos_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(uint8_t v_x_525_){
_start:
{
switch(v_x_525_)
{
case 0:
{
lean_object* v___x_526_; 
v___x_526_ = lean_unsigned_to_nat(0u);
return v___x_526_;
}
case 1:
{
lean_object* v___x_527_; 
v___x_527_ = lean_unsigned_to_nat(1u);
return v___x_527_;
}
default: 
{
lean_object* v___x_528_; 
v___x_528_ = lean_unsigned_to_nat(2u);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___boxed(lean_object* v_x_529_){
_start:
{
uint8_t v_x_boxed_530_; lean_object* v_res_531_; 
v_x_boxed_530_ = lean_unbox(v_x_529_);
v_res_531_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_boxed_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object* v_x_534_){
_start:
{
uint8_t v_x_4__boxed_535_; lean_object* v_res_536_; 
v_x_4__boxed_535_ = lean_unbox(v_x_534_);
v_res_536_ = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(v_x_4__boxed_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(lean_object* v_k_537_){
_start:
{
lean_inc(v_k_537_);
return v_k_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg___boxed(lean_object* v_k_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(v_k_538_);
lean_dec(v_k_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_object* v_motive_540_, lean_object* v_ctorIdx_541_, uint8_t v_t_542_, lean_object* v_h_543_, lean_object* v_k_544_){
_start:
{
lean_inc(v_k_544_);
return v_k_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___boxed(lean_object* v_motive_545_, lean_object* v_ctorIdx_546_, lean_object* v_t_547_, lean_object* v_h_548_, lean_object* v_k_549_){
_start:
{
uint8_t v_t_boxed_550_; lean_object* v_res_551_; 
v_t_boxed_550_ = lean_unbox(v_t_547_);
v_res_551_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(v_motive_545_, v_ctorIdx_546_, v_t_boxed_550_, v_h_548_, v_k_549_);
lean_dec(v_k_549_);
lean_dec(v_ctorIdx_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(lean_object* v_acceptLhs_552_){
_start:
{
lean_inc(v_acceptLhs_552_);
return v_acceptLhs_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg___boxed(lean_object* v_acceptLhs_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(v_acceptLhs_553_);
lean_dec(v_acceptLhs_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_object* v_motive_555_, uint8_t v_t_556_, lean_object* v_h_557_, lean_object* v_acceptLhs_558_){
_start:
{
lean_inc(v_acceptLhs_558_);
return v_acceptLhs_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___boxed(lean_object* v_motive_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_acceptLhs_562_){
_start:
{
uint8_t v_t_boxed_563_; lean_object* v_res_564_; 
v_t_boxed_563_ = lean_unbox(v_t_560_);
v_res_564_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(v_motive_559_, v_t_boxed_563_, v_h_561_, v_acceptLhs_562_);
lean_dec(v_acceptLhs_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(lean_object* v_takeLongest_565_){
_start:
{
lean_inc(v_takeLongest_565_);
return v_takeLongest_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg___boxed(lean_object* v_takeLongest_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(v_takeLongest_566_);
lean_dec(v_takeLongest_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_object* v_motive_568_, uint8_t v_t_569_, lean_object* v_h_570_, lean_object* v_takeLongest_571_){
_start:
{
lean_inc(v_takeLongest_571_);
return v_takeLongest_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___boxed(lean_object* v_motive_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_takeLongest_575_){
_start:
{
uint8_t v_t_boxed_576_; lean_object* v_res_577_; 
v_t_boxed_576_ = lean_unbox(v_t_573_);
v_res_577_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(v_motive_572_, v_t_boxed_576_, v_h_574_, v_takeLongest_575_);
lean_dec(v_takeLongest_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(lean_object* v_merge_578_){
_start:
{
lean_inc(v_merge_578_);
return v_merge_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg___boxed(lean_object* v_merge_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(v_merge_579_);
lean_dec(v_merge_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_object* v_motive_581_, uint8_t v_t_582_, lean_object* v_h_583_, lean_object* v_merge_584_){
_start:
{
lean_inc(v_merge_584_);
return v_merge_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___boxed(lean_object* v_motive_585_, lean_object* v_t_586_, lean_object* v_h_587_, lean_object* v_merge_588_){
_start:
{
uint8_t v_t_boxed_589_; lean_object* v_res_590_; 
v_t_boxed_589_ = lean_unbox(v_t_586_);
v_res_590_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(v_motive_585_, v_t_boxed_589_, v_h_587_, v_merge_588_);
lean_dec(v_merge_588_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(uint8_t v_x_591_, uint8_t v_y_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_x_591_);
v___x_594_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx(v_y_592_);
v___x_595_ = lean_nat_dec_eq(v___x_593_, v___x_594_);
lean_dec(v___x_594_);
lean_dec(v___x_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed(lean_object* v_x_596_, lean_object* v_y_597_){
_start:
{
uint8_t v_x_17__boxed_598_; uint8_t v_y_18__boxed_599_; uint8_t v_res_600_; lean_object* v_r_601_; 
v_x_17__boxed_598_ = lean_unbox(v_x_596_);
v_y_18__boxed_599_ = lean_unbox(v_y_597_);
v_res_600_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_17__boxed_598_, v_y_18__boxed_599_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object* v_stx_607_, lean_object* v_s_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
lean_inc(v_stx_607_);
v___x_610_ = l_Lean_Syntax_isOfKind(v_stx_607_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Parser_ParserState_pushSyntax(v_s_608_, v_stx_607_);
return v___x_611_;
}
else
{
lean_object* v_stxStack_612_; lean_object* v_lhsPrec_613_; lean_object* v_pos_614_; lean_object* v_cache_615_; lean_object* v_errorMsg_616_; lean_object* v_recoveredErrors_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_635_; 
v_stxStack_612_ = lean_ctor_get(v_s_608_, 0);
v_lhsPrec_613_ = lean_ctor_get(v_s_608_, 1);
v_pos_614_ = lean_ctor_get(v_s_608_, 2);
v_cache_615_ = lean_ctor_get(v_s_608_, 3);
v_errorMsg_616_ = lean_ctor_get(v_s_608_, 4);
v_recoveredErrors_617_ = lean_ctor_get(v_s_608_, 5);
v_isSharedCheck_635_ = !lean_is_exclusive(v_s_608_);
if (v_isSharedCheck_635_ == 0)
{
v___x_619_ = v_s_608_;
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_recoveredErrors_617_);
lean_inc(v_errorMsg_616_);
lean_inc(v_cache_615_);
lean_inc(v_pos_614_);
lean_inc(v_lhsPrec_613_);
lean_inc(v_stxStack_612_);
lean_dec(v_s_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_raw_621_; lean_object* v_drop_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_634_; 
v_raw_621_ = lean_ctor_get(v_stxStack_612_, 0);
v_drop_622_ = lean_ctor_get(v_stxStack_612_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_stxStack_612_);
if (v_isSharedCheck_634_ == 0)
{
v___x_624_ = v_stxStack_612_;
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_drop_622_);
lean_inc(v_raw_621_);
lean_dec(v_stxStack_612_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = l_Lean_Syntax_getArgs(v_stx_607_);
lean_dec(v_stx_607_);
v___x_627_ = l_Array_append___redArg(v_raw_621_, v___x_626_);
lean_dec_ref(v___x_626_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_drop_622_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_629_);
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_lhsPrec_613_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_pos_614_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_cache_615_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_errorMsg_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_recoveredErrors_617_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* v_p_636_, lean_object* v_q_637_, uint8_t v_antiquotBehavior_638_, lean_object* v_c_639_, lean_object* v_s_640_){
_start:
{
lean_object* v_pos_641_; lean_object* v_iniSz_642_; lean_object* v_s_643_; lean_object* v_errorMsg_644_; 
v_pos_641_ = lean_ctor_get(v_s_640_, 2);
lean_inc(v_pos_641_);
v_iniSz_642_ = l_Lean_Parser_ParserState_stackSize(v_s_640_);
lean_inc_ref(v_c_639_);
v_s_643_ = lean_apply_2(v_p_636_, v_c_639_, v_s_640_);
v_errorMsg_644_ = lean_ctor_get(v_s_643_, 4);
lean_inc(v_errorMsg_644_);
if (lean_obj_tag(v_errorMsg_644_) == 0)
{
lean_object* v_stxStack_645_; lean_object* v_pos_646_; lean_object* v_pBack_647_; lean_object* v___y_649_; lean_object* v___y_653_; uint8_t v___y_654_; uint8_t v___y_670_; uint8_t v___x_686_; uint8_t v___x_687_; 
v_stxStack_645_ = lean_ctor_get(v_s_643_, 0);
lean_inc_ref(v_stxStack_645_);
v_pos_646_ = lean_ctor_get(v_s_643_, 2);
lean_inc(v_pos_646_);
v_pBack_647_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_645_);
lean_dec_ref(v_stxStack_645_);
v___x_686_ = 0;
v___x_687_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_638_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_688_ = l_Lean_Parser_ParserState_stackSize(v_s_643_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_iniSz_642_, v___x_689_);
v___x_691_ = lean_nat_dec_eq(v___x_688_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_688_);
v___x_692_ = lean_bool_not(v___x_691_);
v___y_670_ = v___x_692_;
goto v___jp_669_;
}
else
{
v___y_670_ = v___x_687_;
goto v___jp_669_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_Lean_Parser_ParserState_restore(v___y_649_, v_iniSz_642_, v_pos_646_);
lean_dec(v_iniSz_642_);
v___x_651_ = l_Lean_Parser_ParserState_pushSyntax(v___x_650_, v_pBack_647_);
return v___x_651_;
}
v___jp_652_:
{
if (v___y_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; uint8_t v___x_659_; 
v___x_655_ = l_Lean_Parser_ParserState_stackSize(v___y_653_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_iniSz_642_, v___x_656_);
v___x_658_ = lean_nat_dec_eq(v___x_655_, v___x_657_);
lean_dec(v___x_657_);
lean_dec(v___x_655_);
v___x_659_ = lean_bool_not(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v_stxStack_660_; lean_object* v___x_661_; uint8_t v___x_662_; uint8_t v___x_663_; 
v_stxStack_660_ = lean_ctor_get(v___y_653_, 0);
v___x_661_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_660_);
lean_inc(v___x_661_);
v___x_662_ = l_Lean_Syntax_isAntiquots(v___x_661_);
v___x_663_ = lean_bool_not(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v_s_664_; lean_object* v_s_665_; lean_object* v_s_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_pos_646_);
v_s_664_ = l_Lean_Parser_ParserState_popSyntax(v___y_653_);
v_s_665_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_647_, v_s_664_);
v_s_666_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_661_, v_s_665_);
v___x_667_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_668_ = l_Lean_Parser_ParserState_mkNode(v_s_666_, v___x_667_, v_iniSz_642_);
lean_dec(v_iniSz_642_);
return v___x_668_;
}
else
{
lean_dec(v___x_661_);
v___y_649_ = v___y_653_;
goto v___jp_648_;
}
}
else
{
v___y_649_ = v___y_653_;
goto v___jp_648_;
}
}
else
{
v___y_649_ = v___y_653_;
goto v___jp_648_;
}
}
v___jp_669_:
{
if (v___y_670_ == 0)
{
uint8_t v___x_671_; uint8_t v___x_672_; 
lean_inc(v_pBack_647_);
v___x_671_ = l_Lean_Syntax_isAntiquots(v_pBack_647_);
v___x_672_ = lean_bool_not(v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v_s_673_; lean_object* v_s_674_; lean_object* v_pos_675_; lean_object* v_errorMsg_676_; uint8_t v___x_677_; uint8_t v___x_678_; 
v_s_673_ = l_Lean_Parser_ParserState_restore(v_s_643_, v_iniSz_642_, v_pos_641_);
v_s_674_ = lean_apply_2(v_q_637_, v_c_639_, v_s_673_);
v_pos_675_ = lean_ctor_get(v_s_674_, 2);
lean_inc(v_pos_675_);
v_errorMsg_676_ = lean_ctor_get(v_s_674_, 4);
lean_inc(v_errorMsg_676_);
v___x_677_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_676_, v_errorMsg_644_);
v___x_678_ = lean_bool_not(v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_lt(v_pos_646_, v_pos_675_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_lt(v_pos_675_, v_pos_646_);
lean_dec(v_pos_675_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_681_ = 2;
v___x_682_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_638_, v___x_681_);
v___x_683_ = lean_bool_not(v___x_682_);
v___y_653_ = v_s_674_;
v___y_654_ = v___x_683_;
goto v___jp_652_;
}
else
{
v___y_653_ = v_s_674_;
v___y_654_ = v___x_680_;
goto v___jp_652_;
}
}
else
{
lean_dec(v_pos_675_);
lean_dec(v_pBack_647_);
lean_dec(v_pos_646_);
lean_dec(v_iniSz_642_);
return v_s_674_;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec(v_pos_675_);
v___x_684_ = l_Lean_Parser_ParserState_restore(v_s_674_, v_iniSz_642_, v_pos_646_);
lean_dec(v_iniSz_642_);
v___x_685_ = l_Lean_Parser_ParserState_pushSyntax(v___x_684_, v_pBack_647_);
return v___x_685_;
}
}
else
{
lean_dec(v_pBack_647_);
lean_dec(v_pos_646_);
lean_dec(v_iniSz_642_);
lean_dec(v_pos_641_);
lean_dec_ref(v_c_639_);
lean_dec_ref(v_q_637_);
return v_s_643_;
}
}
else
{
lean_dec(v_pBack_647_);
lean_dec(v_pos_646_);
lean_dec(v_iniSz_642_);
lean_dec(v_pos_641_);
lean_dec_ref(v_c_639_);
lean_dec_ref(v_q_637_);
return v_s_643_;
}
}
}
else
{
lean_object* v_pos_693_; lean_object* v_val_694_; uint8_t v___x_695_; 
v_pos_693_ = lean_ctor_get(v_s_643_, 2);
lean_inc(v_pos_693_);
v_val_694_ = lean_ctor_get(v_errorMsg_644_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_errorMsg_644_, 1);
v___x_695_ = lean_nat_dec_eq(v_pos_693_, v_pos_641_);
lean_dec(v_pos_693_);
if (v___x_695_ == 0)
{
lean_dec(v_val_694_);
lean_dec(v_iniSz_642_);
lean_dec(v_pos_641_);
lean_dec_ref(v_c_639_);
lean_dec_ref(v_q_637_);
return v_s_643_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc(v_pos_641_);
v___x_696_ = l_Lean_Parser_ParserState_restore(v_s_643_, v_iniSz_642_, v_pos_641_);
lean_dec(v_iniSz_642_);
v___x_697_ = lean_apply_2(v_q_637_, v_c_639_, v___x_696_);
v___x_698_ = l_Lean_Parser_mergeOrElseErrors(v___x_697_, v_val_694_, v_pos_641_, v___x_695_);
lean_dec(v_pos_641_);
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_699_, lean_object* v_q_700_, lean_object* v_antiquotBehavior_701_, lean_object* v_c_702_, lean_object* v_s_703_){
_start:
{
uint8_t v_antiquotBehavior_boxed_704_; lean_object* v_res_705_; 
v_antiquotBehavior_boxed_704_ = lean_unbox(v_antiquotBehavior_701_);
v_res_705_ = l_Lean_Parser_orelseFnCore(v_p_699_, v_q_700_, v_antiquotBehavior_boxed_704_, v_c_702_, v_s_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_706_, lean_object* v_q_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
uint8_t v___x_710_; lean_object* v___x_711_; 
v___x_710_ = 2;
v___x_711_ = l_Lean_Parser_orelseFnCore(v_p_706_, v_q_707_, v___x_710_, v_a_708_, v_a_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_712_, lean_object* v_q_713_){
_start:
{
lean_object* v_collectTokens_714_; lean_object* v_collectKinds_715_; lean_object* v_firstTokens_716_; lean_object* v_collectTokens_717_; lean_object* v_collectKinds_718_; lean_object* v_firstTokens_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_729_; 
v_collectTokens_714_ = lean_ctor_get(v_p_712_, 0);
lean_inc_ref(v_collectTokens_714_);
v_collectKinds_715_ = lean_ctor_get(v_p_712_, 1);
lean_inc_ref(v_collectKinds_715_);
v_firstTokens_716_ = lean_ctor_get(v_p_712_, 2);
lean_inc(v_firstTokens_716_);
lean_dec_ref(v_p_712_);
v_collectTokens_717_ = lean_ctor_get(v_q_713_, 0);
v_collectKinds_718_ = lean_ctor_get(v_q_713_, 1);
v_firstTokens_719_ = lean_ctor_get(v_q_713_, 2);
v_isSharedCheck_729_ = !lean_is_exclusive(v_q_713_);
if (v_isSharedCheck_729_ == 0)
{
v___x_721_ = v_q_713_;
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_firstTokens_719_);
lean_inc(v_collectKinds_718_);
lean_inc(v_collectTokens_717_);
lean_dec(v_q_713_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___f_723_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_723_, 0, v_collectKinds_718_);
lean_closure_set(v___f_723_, 1, v_collectKinds_715_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_724_, 0, v_collectTokens_717_);
lean_closure_set(v___f_724_, 1, v_collectTokens_714_);
v___x_725_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_716_, v_firstTokens_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 2, v___x_725_);
lean_ctor_set(v___x_721_, 1, v___f_723_);
lean_ctor_set(v___x_721_, 0, v___f_724_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___f_724_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___f_723_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_730_, lean_object* v_p2_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
v___x_735_ = lean_apply_1(v_p2_731_, v___x_734_);
v___x_736_ = l_Lean_Parser_orelseFn(v_p1_730_, v___x_735_, v___y_732_, v___y_733_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_739_, lean_object* v_q_740_){
_start:
{
lean_object* v_info_741_; lean_object* v_fn_742_; lean_object* v_info_743_; lean_object* v_fn_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_753_; 
v_info_741_ = lean_ctor_get(v_p_739_, 0);
lean_inc_ref(v_info_741_);
v_fn_742_ = lean_ctor_get(v_p_739_, 1);
lean_inc_ref(v_fn_742_);
lean_dec_ref(v_p_739_);
v_info_743_ = lean_ctor_get(v_q_740_, 0);
v_fn_744_ = lean_ctor_get(v_q_740_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_q_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_746_ = v_q_740_;
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_fn_744_);
lean_inc(v_info_743_);
lean_dec(v_q_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = l_Lean_Parser_orelseInfo(v_info_741_, v_info_743_);
v___x_749_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_749_, 0, v_fn_742_);
lean_closure_set(v___x_749_, 1, v_fn_744_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_749_);
lean_ctor_set(v___x_746_, 0, v___x_748_);
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_762_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_763_ = l_Lean_addBuiltinDocString(v___x_761_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_766_, lean_object* v_b_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_apply_1(v_b_767_, v___x_768_);
v___x_770_ = l_Lean_Parser_orelse(v_a_766_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_773_){
_start:
{
lean_object* v_collectTokens_774_; lean_object* v_collectKinds_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_783_; 
v_collectTokens_774_ = lean_ctor_get(v_info_773_, 0);
v_collectKinds_775_ = lean_ctor_get(v_info_773_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_info_773_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_info_773_, 2);
lean_dec(v_unused_784_);
v___x_777_ = v_info_773_;
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_collectKinds_775_);
lean_inc(v_collectTokens_774_);
lean_dec(v_info_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_box(1);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 2, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_collectTokens_774_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_collectKinds_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_785_, lean_object* v_c_786_, lean_object* v_s_787_){
_start:
{
lean_object* v_pos_788_; lean_object* v___x_789_; lean_object* v_errorMsg_790_; 
v_pos_788_ = lean_ctor_get(v_s_787_, 2);
lean_inc(v_pos_788_);
v___x_789_ = lean_apply_2(v_p_785_, v_c_786_, v_s_787_);
v_errorMsg_790_ = lean_ctor_get(v___x_789_, 4);
lean_inc(v_errorMsg_790_);
if (lean_obj_tag(v_errorMsg_790_) == 1)
{
lean_object* v_stxStack_791_; lean_object* v_lhsPrec_792_; lean_object* v_cache_793_; lean_object* v_recoveredErrors_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_stxStack_791_ = lean_ctor_get(v___x_789_, 0);
v_lhsPrec_792_ = lean_ctor_get(v___x_789_, 1);
v_cache_793_ = lean_ctor_get(v___x_789_, 3);
v_recoveredErrors_794_ = lean_ctor_get(v___x_789_, 5);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_802_ = lean_ctor_get(v___x_789_, 4);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v___x_789_, 2);
lean_dec(v_unused_803_);
v___x_796_ = v___x_789_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_recoveredErrors_794_);
lean_inc(v_cache_793_);
lean_inc(v_lhsPrec_792_);
lean_inc(v_stxStack_791_);
lean_dec(v___x_789_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 2, v_pos_788_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_stxStack_791_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_lhsPrec_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_pos_788_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_cache_793_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_errorMsg_790_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v_recoveredErrors_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_dec(v_errorMsg_790_);
lean_dec(v_pos_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_804_){
_start:
{
lean_object* v_info_805_; lean_object* v_fn_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_info_805_ = lean_ctor_get(v_p_804_, 0);
v_fn_806_ = lean_ctor_get(v_p_804_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_p_804_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v_p_804_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_fn_806_);
lean_inc(v_info_805_);
lean_dec(v_p_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_810_, 0, v_fn_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_info_805_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_823_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_824_ = l_Lean_addBuiltinDocString(v___x_822_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_826_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_827_, lean_object* v_x_828_){
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
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_835_, v_x_836_);
lean_dec_ref(v_x_836_);
lean_dec_ref(v_x_835_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_initialPos_843_; lean_object* v_initialSize_844_; lean_object* v_initialPos_845_; lean_object* v_initialSize_846_; uint8_t v___x_847_; 
v_initialPos_843_ = lean_ctor_get(v_x_841_, 0);
v_initialSize_844_ = lean_ctor_get(v_x_841_, 1);
v_initialPos_845_ = lean_ctor_get(v_x_842_, 0);
v_initialSize_846_ = lean_ctor_get(v_x_842_, 1);
v___x_847_ = lean_nat_dec_eq(v_initialPos_843_, v_initialPos_845_);
if (v___x_847_ == 0)
{
return v___x_847_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = lean_nat_dec_eq(v_initialSize_844_, v_initialSize_846_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_849_, v_x_850_);
lean_dec_ref(v_x_850_);
lean_dec_ref(v_x_849_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
uint8_t v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_856_, v_x_857_);
lean_dec_ref(v_x_857_);
lean_dec_ref(v_x_856_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(14u);
v___x_874_ = lean_nat_to_int(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_unsigned_to_nat(15u);
v___x_888_ = lean_nat_to_int(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_890_ = lean_string_length(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_892_ = lean_nat_to_int(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_895_){
_start:
{
lean_object* v_initialPos_896_; lean_object* v_initialSize_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_935_; 
v_initialPos_896_ = lean_ctor_get(v_x_895_, 0);
v_initialSize_897_ = lean_ctor_get(v_x_895_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_935_ == 0)
{
v___x_899_ = v_x_895_;
v_isShared_900_ = v_isSharedCheck_935_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_initialSize_897_);
lean_inc(v_initialPos_896_);
lean_dec(v_x_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_935_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_901_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_902_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_903_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_904_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_905_ = l_Nat_reprFast(v_initialPos_896_);
v___x_906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 5);
lean_ctor_set(v___x_899_, 1, v___x_906_);
lean_ctor_set(v___x_899_, 0, v___x_904_);
v___x_908_ = v___x_899_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_906_);
v___x_908_ = v_reuseFailAlloc_934_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_909_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_903_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = 0;
v___x_913_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_912_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_902_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_box(1);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_901_);
v___x_922_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_923_ = l_Nat_reprFast(v_initialSize_897_);
v___x_924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_922_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*1, v___x_912_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_921_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_929_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_927_);
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_909_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_912_);
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_936_, lean_object* v_prec_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_939_, lean_object* v_prec_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_939_, v_prec_940_);
lean_dec(v_prec_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_944_, lean_object* v_recover_945_, lean_object* v_c_946_, lean_object* v_s_947_){
_start:
{
lean_object* v_stxStack_948_; lean_object* v_pos_949_; lean_object* v_s_950_; lean_object* v_errorMsg_951_; 
v_stxStack_948_ = lean_ctor_get(v_s_947_, 0);
lean_inc_ref(v_stxStack_948_);
v_pos_949_ = lean_ctor_get(v_s_947_, 2);
lean_inc(v_pos_949_);
lean_inc_ref(v_c_946_);
v_s_950_ = lean_apply_2(v_p_944_, v_c_946_, v_s_947_);
v_errorMsg_951_ = lean_ctor_get(v_s_950_, 4);
lean_inc(v_errorMsg_951_);
if (lean_obj_tag(v_errorMsg_951_) == 1)
{
lean_object* v_stxStack_952_; lean_object* v_lhsPrec_953_; lean_object* v_pos_954_; lean_object* v_cache_955_; lean_object* v_recoveredErrors_956_; lean_object* v_val_957_; lean_object* v_iniSz_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_s_x27_962_; lean_object* v_stxStack_963_; lean_object* v_pos_964_; lean_object* v_errorMsg_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_977_; 
v_stxStack_952_ = lean_ctor_get(v_s_950_, 0);
lean_inc_ref(v_stxStack_952_);
v_lhsPrec_953_ = lean_ctor_get(v_s_950_, 1);
lean_inc_n(v_lhsPrec_953_, 2);
v_pos_954_ = lean_ctor_get(v_s_950_, 2);
lean_inc(v_pos_954_);
v_cache_955_ = lean_ctor_get(v_s_950_, 3);
lean_inc_ref_n(v_cache_955_, 2);
v_recoveredErrors_956_ = lean_ctor_get(v_s_950_, 5);
lean_inc_ref_n(v_recoveredErrors_956_, 2);
v_val_957_ = lean_ctor_get(v_errorMsg_951_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_errorMsg_951_, 1);
v_iniSz_958_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_948_);
lean_dec_ref(v_stxStack_948_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_pos_949_);
lean_ctor_set(v___x_959_, 1, v_iniSz_958_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_961_, 0, v_stxStack_952_);
lean_ctor_set(v___x_961_, 1, v_lhsPrec_953_);
lean_ctor_set(v___x_961_, 2, v_pos_954_);
lean_ctor_set(v___x_961_, 3, v_cache_955_);
lean_ctor_set(v___x_961_, 4, v___x_960_);
lean_ctor_set(v___x_961_, 5, v_recoveredErrors_956_);
v_s_x27_962_ = lean_apply_3(v_recover_945_, v___x_959_, v_c_946_, v___x_961_);
v_stxStack_963_ = lean_ctor_get(v_s_x27_962_, 0);
v_pos_964_ = lean_ctor_get(v_s_x27_962_, 2);
v_errorMsg_965_ = lean_ctor_get(v_s_x27_962_, 4);
v_isSharedCheck_977_ = !lean_is_exclusive(v_s_x27_962_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_978_ = lean_ctor_get(v_s_x27_962_, 5);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_s_x27_962_, 3);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_s_x27_962_, 1);
lean_dec(v_unused_980_);
v___x_967_ = v_s_x27_962_;
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_errorMsg_965_);
lean_inc(v_pos_964_);
lean_inc(v_stxStack_963_);
lean_dec(v_s_x27_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_965_, v___x_960_);
v___x_970_ = lean_bool_not(v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec_ref(v_s_950_);
lean_inc_ref(v_stxStack_963_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_stxStack_963_);
lean_ctor_set(v___x_971_, 1, v_val_957_);
lean_inc(v_pos_964_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_pos_964_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_array_push(v_recoveredErrors_956_, v___x_972_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 5, v___x_973_);
lean_ctor_set(v___x_967_, 4, v___x_960_);
lean_ctor_set(v___x_967_, 3, v_cache_955_);
lean_ctor_set(v___x_967_, 1, v_lhsPrec_953_);
v___x_975_ = v___x_967_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_stxStack_963_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_lhsPrec_953_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_pos_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_cache_955_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_976_, 5, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_del_object(v___x_967_);
lean_dec(v_pos_964_);
lean_dec_ref(v_stxStack_963_);
lean_dec(v_val_957_);
lean_dec_ref(v_recoveredErrors_956_);
lean_dec_ref(v_cache_955_);
lean_dec(v_lhsPrec_953_);
return v_s_950_;
}
}
}
else
{
lean_dec(v_errorMsg_951_);
lean_dec(v_pos_949_);
lean_dec_ref(v_stxStack_948_);
lean_dec_ref(v_c_946_);
lean_dec_ref(v_recover_945_);
return v_s_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_981_, lean_object* v_s_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_985_; lean_object* v_fn_986_; lean_object* v___x_987_; 
v___x_985_ = lean_apply_1(v_handler_981_, v_s_982_);
v_fn_986_ = lean_ctor_get(v___x_985_, 1);
lean_inc_ref(v_fn_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_apply_2(v_fn_986_, v___y_983_, v___y_984_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_988_, lean_object* v_handler_989_){
_start:
{
lean_object* v_info_990_; lean_object* v_fn_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
v_info_990_ = lean_ctor_get(v_parser_988_, 0);
v_fn_991_ = lean_ctor_get(v_parser_988_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_parser_988_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_993_ = v_parser_988_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_fn_991_);
lean_inc(v_info_990_);
lean_dec(v_parser_988_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___f_995_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_995_, 0, v_handler_989_);
v___x_996_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_996_, 0, v_fn_991_);
lean_closure_set(v___x_996_, 1, v___f_995_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_info_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_1009_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_1010_ = l_Lean_addBuiltinDocString(v___x_1008_, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_1013_, lean_object* v_x_1014_){
_start:
{
lean_inc_ref(v_handler_1013_);
return v_handler_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Parser_recover___lam__0(v_handler_1015_, v_x_1016_);
lean_dec_ref(v_x_1016_);
lean_dec_ref(v_handler_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1018_, lean_object* v_handler_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1020_, 0, v_handler_1019_);
v___x_1021_ = l_Lean_Parser_recover_x27(v_parser_1018_, v___f_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1030_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1031_ = l_Lean_addBuiltinDocString(v___x_1029_, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1037_, lean_object* v_c_1038_, lean_object* v_s_1039_){
_start:
{
lean_object* v_pos_1040_; lean_object* v_iniSz_1041_; lean_object* v___y_1043_; lean_object* v_s_1046_; uint8_t v___y_1048_; lean_object* v_pos_1050_; lean_object* v_errorMsg_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; 
v_pos_1040_ = lean_ctor_get(v_s_1039_, 2);
lean_inc(v_pos_1040_);
v_iniSz_1041_ = l_Lean_Parser_ParserState_stackSize(v_s_1039_);
v_s_1046_ = lean_apply_2(v_p_1037_, v_c_1038_, v_s_1039_);
v_pos_1050_ = lean_ctor_get(v_s_1046_, 2);
lean_inc(v_pos_1050_);
v_errorMsg_1051_ = lean_ctor_get(v_s_1046_, 4);
lean_inc(v_errorMsg_1051_);
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1051_, v___x_1052_);
v___x_1054_ = lean_bool_not(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v_pos_1050_);
v___y_1048_ = v___x_1054_;
goto v___jp_1047_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_nat_dec_eq(v_pos_1050_, v_pos_1040_);
lean_dec(v_pos_1050_);
v___y_1048_ = v___x_1055_;
goto v___jp_1047_;
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1045_ = l_Lean_Parser_ParserState_mkNode(v___y_1043_, v___x_1044_, v_iniSz_1041_);
lean_dec(v_iniSz_1041_);
return v___x_1045_;
}
v___jp_1047_:
{
if (v___y_1048_ == 0)
{
lean_dec(v_pos_1040_);
v___y_1043_ = v_s_1046_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Parser_ParserState_restore(v_s_1046_, v_iniSz_1041_, v_pos_1040_);
v___y_1043_ = v___x_1049_;
goto v___jp_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1056_){
_start:
{
lean_object* v_collectTokens_1057_; lean_object* v_collectKinds_1058_; lean_object* v_firstTokens_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_collectTokens_1057_ = lean_ctor_get(v_p_1056_, 0);
v_collectKinds_1058_ = lean_ctor_get(v_p_1056_, 1);
v_firstTokens_1059_ = lean_ctor_get(v_p_1056_, 2);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_p_1056_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v_p_1056_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_firstTokens_1059_);
lean_inc(v_collectKinds_1058_);
lean_inc(v_collectTokens_1057_);
lean_dec(v_p_1056_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 2, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_collectTokens_1057_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_collectKinds_1058_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1068_){
_start:
{
lean_object* v_info_1069_; lean_object* v_fn_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1079_; 
v_info_1069_ = lean_ctor_get(v_p_1068_, 0);
v_fn_1070_ = lean_ctor_get(v_p_1068_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_p_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1072_ = v_p_1068_;
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_fn_1070_);
lean_inc(v_info_1069_);
lean_dec(v_p_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = l_Lean_Parser_optionalInfo(v_info_1069_);
v___x_1075_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1075_, 0, v_fn_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___x_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1080_, lean_object* v_c_1081_, lean_object* v_s_1082_){
_start:
{
lean_object* v_pos_1083_; lean_object* v_iniSz_1084_; lean_object* v_s_1085_; lean_object* v_errorMsg_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; uint8_t v___x_1089_; 
v_pos_1083_ = lean_ctor_get(v_s_1082_, 2);
lean_inc(v_pos_1083_);
v_iniSz_1084_ = l_Lean_Parser_ParserState_stackSize(v_s_1082_);
v_s_1085_ = lean_apply_2(v_p_1080_, v_c_1081_, v_s_1082_);
v_errorMsg_1086_ = lean_ctor_get(v_s_1085_, 4);
lean_inc(v_errorMsg_1086_);
v___x_1087_ = lean_box(0);
v___x_1088_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1086_, v___x_1087_);
v___x_1089_ = lean_bool_not(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Parser_ParserState_restore(v_s_1085_, v_iniSz_1084_, v_pos_1083_);
lean_dec(v_iniSz_1084_);
return v___x_1090_;
}
else
{
lean_dec(v_iniSz_1084_);
lean_dec(v_pos_1083_);
return v_s_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1091_){
_start:
{
lean_object* v_info_1092_; lean_object* v_fn_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
v_info_1092_ = lean_ctor_get(v_p_1091_, 0);
v_fn_1093_ = lean_ctor_get(v_p_1091_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_p_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v_p_1091_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_fn_1093_);
lean_inc(v_info_1092_);
lean_dec(v_p_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1097_, 0, v_fn_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_info_1092_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1110_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1111_ = l_Lean_addBuiltinDocString(v___x_1109_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1115_, lean_object* v_msg_1116_, lean_object* v_c_1117_, lean_object* v_s_1118_){
_start:
{
lean_object* v_pos_1119_; lean_object* v_iniSz_1120_; lean_object* v_s_1121_; lean_object* v_errorMsg_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; uint8_t v___x_1125_; 
v_pos_1119_ = lean_ctor_get(v_s_1118_, 2);
lean_inc(v_pos_1119_);
v_iniSz_1120_ = l_Lean_Parser_ParserState_stackSize(v_s_1118_);
v_s_1121_ = lean_apply_2(v_p_1115_, v_c_1117_, v_s_1118_);
v_errorMsg_1122_ = lean_ctor_get(v_s_1121_, 4);
lean_inc(v_errorMsg_1122_);
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1122_, v___x_1123_);
v___x_1125_ = lean_bool_not(v___x_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; lean_object* v_s_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1126_ = 1;
v_s_1127_ = l_Lean_Parser_ParserState_restore(v_s_1121_, v_iniSz_1120_, v_pos_1119_);
lean_dec(v_iniSz_1120_);
v___x_1128_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1129_ = lean_string_append(v___x_1128_, v_msg_1116_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1127_, v___x_1129_, v___x_1130_, v___x_1126_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Parser_ParserState_restore(v_s_1121_, v_iniSz_1120_, v_pos_1119_);
lean_dec(v_iniSz_1120_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1133_, lean_object* v_msg_1134_, lean_object* v_c_1135_, lean_object* v_s_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Parser_notFollowedByFn(v_p_1133_, v_msg_1134_, v_c_1135_, v_s_1136_);
lean_dec_ref(v_msg_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1138_, lean_object* v_msg_1139_){
_start:
{
lean_object* v_fn_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1149_; 
v_fn_1140_ = lean_ctor_get(v_p_1138_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_p_1138_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_p_1138_, 0);
lean_dec(v_unused_1150_);
v___x_1142_ = v_p_1138_;
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_fn_1140_);
lean_dec(v_p_1138_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1145_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1145_, 0, v_fn_1140_);
lean_closure_set(v___x_1145_, 1, v_msg_1139_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1145_);
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1159_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1160_ = l_Lean_addBuiltinDocString(v___x_1158_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1164_, lean_object* v_c_1165_, lean_object* v_s_1166_){
_start:
{
lean_object* v_pos_1167_; lean_object* v_iniSz_1168_; lean_object* v_s_1169_; lean_object* v_pos_1170_; lean_object* v_errorMsg_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; uint8_t v___x_1174_; 
v_pos_1167_ = lean_ctor_get(v_s_1166_, 2);
lean_inc(v_pos_1167_);
v_iniSz_1168_ = l_Lean_Parser_ParserState_stackSize(v_s_1166_);
lean_inc_ref(v_p_1164_);
lean_inc_ref(v_c_1165_);
v_s_1169_ = lean_apply_2(v_p_1164_, v_c_1165_, v_s_1166_);
v_pos_1170_ = lean_ctor_get(v_s_1169_, 2);
lean_inc(v_pos_1170_);
v_errorMsg_1171_ = lean_ctor_get(v_s_1169_, 4);
lean_inc(v_errorMsg_1171_);
v___x_1172_ = lean_box(0);
v___x_1173_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1171_, v___x_1172_);
v___x_1174_ = lean_bool_not(v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_eq(v_pos_1167_, v_pos_1170_);
lean_dec(v_pos_1170_);
lean_dec(v_pos_1167_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_add(v_iniSz_1168_, v___x_1176_);
v___x_1178_ = l_Lean_Parser_ParserState_stackSize(v_s_1169_);
v___x_1179_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
lean_dec(v___x_1178_);
lean_dec(v___x_1177_);
if (v___x_1179_ == 0)
{
lean_dec(v_iniSz_1168_);
v_s_1166_ = v_s_1169_;
goto _start;
}
else
{
lean_object* v___x_1181_; lean_object* v_s_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1182_ = l_Lean_Parser_ParserState_mkNode(v_s_1169_, v___x_1181_, v_iniSz_1168_);
lean_dec(v_iniSz_1168_);
v_s_1166_ = v_s_1182_;
goto _start;
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_iniSz_1168_);
lean_dec_ref(v_c_1165_);
lean_dec_ref(v_p_1164_);
v___x_1184_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1169_, v___x_1184_, v___x_1185_, v___x_1175_);
return v___x_1186_;
}
}
else
{
uint8_t v___x_1187_; 
lean_dec_ref(v_c_1165_);
lean_dec_ref(v_p_1164_);
v___x_1187_ = lean_nat_dec_eq(v_pos_1167_, v_pos_1170_);
lean_dec(v_pos_1170_);
if (v___x_1187_ == 0)
{
lean_dec(v_iniSz_1168_);
lean_dec(v_pos_1167_);
return v_s_1169_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Parser_ParserState_restore(v_s_1169_, v_iniSz_1168_, v_pos_1167_);
lean_dec(v_iniSz_1168_);
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1189_, lean_object* v_c_1190_, lean_object* v_s_1191_){
_start:
{
lean_object* v_iniSz_1192_; lean_object* v_s_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_iniSz_1192_ = l_Lean_Parser_ParserState_stackSize(v_s_1191_);
v_s_1193_ = l_Lean_Parser_manyAux(v_p_1189_, v_c_1190_, v_s_1191_);
v___x_1194_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1195_ = l_Lean_Parser_ParserState_mkNode(v_s_1193_, v___x_1194_, v_iniSz_1192_);
lean_dec(v_iniSz_1192_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1196_){
_start:
{
lean_object* v_info_1197_; lean_object* v_fn_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1207_; 
v_info_1197_ = lean_ctor_get(v_p_1196_, 0);
v_fn_1198_ = lean_ctor_get(v_p_1196_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_p_1196_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1200_ = v_p_1196_;
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_fn_1198_);
lean_inc(v_info_1197_);
lean_dec(v_p_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_Parser_noFirstTokenInfo(v_info_1197_);
v___x_1203_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1203_, 0, v_fn_1198_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1208_, lean_object* v_c_1209_, lean_object* v_s_1210_){
_start:
{
lean_object* v_iniSz_1211_; lean_object* v___x_1212_; lean_object* v_s_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_iniSz_1211_ = l_Lean_Parser_ParserState_stackSize(v_s_1210_);
lean_inc_ref(v_p_1208_);
v___x_1212_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1212_, 0, v_p_1208_);
v_s_1213_ = l_Lean_Parser_andthenFn(v_p_1208_, v___x_1212_, v_c_1209_, v_s_1210_);
v___x_1214_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1215_ = l_Lean_Parser_ParserState_mkNode(v_s_1213_, v___x_1214_, v_iniSz_1211_);
lean_dec(v_iniSz_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1216_){
_start:
{
lean_object* v_info_1217_; lean_object* v_fn_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_info_1217_ = lean_ctor_get(v_p_1216_, 0);
v_fn_1218_ = lean_ctor_get(v_p_1216_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_p_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v_p_1216_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_fn_1218_);
lean_inc(v_info_1217_);
lean_dec(v_p_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1222_, 0, v_fn_1218_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_info_1217_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1227_, lean_object* v_sep_1228_, uint8_t v_allowTrailingSep_1229_, lean_object* v_iniSz_1230_, uint8_t v_pOpt_1231_, lean_object* v_c_1232_, lean_object* v_s_1233_){
_start:
{
lean_object* v_s_1235_; lean_object* v_pos_1236_; lean_object* v_pos_1254_; lean_object* v_sz_1255_; lean_object* v_s_1256_; lean_object* v_pos_1257_; lean_object* v_errorMsg_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; uint8_t v___x_1261_; 
v_pos_1254_ = lean_ctor_get(v_s_1233_, 2);
lean_inc(v_pos_1254_);
v_sz_1255_ = l_Lean_Parser_ParserState_stackSize(v_s_1233_);
lean_inc_ref(v_p_1227_);
lean_inc_ref(v_c_1232_);
v_s_1256_ = lean_apply_2(v_p_1227_, v_c_1232_, v_s_1233_);
v_pos_1257_ = lean_ctor_get(v_s_1256_, 2);
lean_inc(v_pos_1257_);
v_errorMsg_1258_ = lean_ctor_get(v_s_1256_, 4);
lean_inc(v_errorMsg_1258_);
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1258_, v___x_1259_);
v___x_1261_ = lean_bool_not(v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
lean_dec(v_pos_1254_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v_sz_1255_, v___x_1262_);
v___x_1264_ = l_Lean_Parser_ParserState_stackSize(v_s_1256_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
lean_dec(v___x_1264_);
lean_dec(v___x_1263_);
if (v___x_1265_ == 0)
{
lean_dec(v_sz_1255_);
v_s_1235_ = v_s_1256_;
v_pos_1236_ = v_pos_1257_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1266_; lean_object* v_s_1267_; lean_object* v_pos_1268_; 
lean_dec(v_pos_1257_);
v___x_1266_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1267_ = l_Lean_Parser_ParserState_mkNode(v_s_1256_, v___x_1266_, v_sz_1255_);
lean_dec(v_sz_1255_);
v_pos_1268_ = lean_ctor_get(v_s_1267_, 2);
lean_inc(v_pos_1268_);
v_s_1235_ = v_s_1267_;
v_pos_1236_ = v_pos_1268_;
goto v___jp_1234_;
}
}
else
{
uint8_t v___x_1269_; 
lean_dec_ref(v_c_1232_);
lean_dec_ref(v_sep_1228_);
lean_dec_ref(v_p_1227_);
v___x_1269_ = lean_nat_dec_lt(v_pos_1254_, v_pos_1257_);
lean_dec(v_pos_1257_);
if (v___x_1269_ == 0)
{
if (v_pOpt_1231_ == 0)
{
lean_object* v___x_1270_; lean_object* v_s_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec(v_sz_1255_);
lean_dec(v_pos_1254_);
v___x_1270_ = lean_box(0);
v_s_1271_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1256_, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1273_ = l_Lean_Parser_ParserState_mkNode(v_s_1271_, v___x_1272_, v_iniSz_1230_);
return v___x_1273_;
}
else
{
lean_object* v_s_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_s_1274_ = l_Lean_Parser_ParserState_restore(v_s_1256_, v_sz_1255_, v_pos_1254_);
lean_dec(v_sz_1255_);
v___x_1275_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1276_ = l_Lean_Parser_ParserState_mkNode(v_s_1274_, v___x_1275_, v_iniSz_1230_);
return v___x_1276_;
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_sz_1255_);
lean_dec(v_pos_1254_);
v___x_1277_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1278_ = l_Lean_Parser_ParserState_mkNode(v_s_1256_, v___x_1277_, v_iniSz_1230_);
return v___x_1278_;
}
}
v___jp_1234_:
{
lean_object* v_sz_1237_; lean_object* v_s_1238_; lean_object* v_errorMsg_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; uint8_t v___x_1242_; 
v_sz_1237_ = l_Lean_Parser_ParserState_stackSize(v_s_1235_);
lean_inc_ref(v_sep_1228_);
lean_inc_ref(v_c_1232_);
v_s_1238_ = lean_apply_2(v_sep_1228_, v_c_1232_, v_s_1235_);
v_errorMsg_1239_ = lean_ctor_get(v_s_1238_, 4);
lean_inc(v_errorMsg_1239_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1239_, v___x_1240_);
v___x_1242_ = lean_bool_not(v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
lean_dec(v_pos_1236_);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_sz_1237_, v___x_1243_);
v___x_1245_ = l_Lean_Parser_ParserState_stackSize(v_s_1238_);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
lean_dec(v___x_1245_);
lean_dec(v___x_1244_);
if (v___x_1246_ == 0)
{
lean_dec(v_sz_1237_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1229_;
lean_object* _tmp_6 = v_s_1238_;
v_pOpt_1231_ = _tmp_4;
v_s_1233_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1248_; lean_object* v_s_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1249_ = l_Lean_Parser_ParserState_mkNode(v_s_1238_, v___x_1248_, v_sz_1237_);
lean_dec(v_sz_1237_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1229_;
lean_object* _tmp_6 = v_s_1249_;
v_pOpt_1231_ = _tmp_4;
v_s_1233_ = _tmp_6;
}
goto _start;
}
}
else
{
lean_object* v_s_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v_c_1232_);
lean_dec_ref(v_sep_1228_);
lean_dec_ref(v_p_1227_);
v_s_1251_ = l_Lean_Parser_ParserState_restore(v_s_1238_, v_sz_1237_, v_pos_1236_);
lean_dec(v_sz_1237_);
v___x_1252_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1253_ = l_Lean_Parser_ParserState_mkNode(v_s_1251_, v___x_1252_, v_iniSz_1230_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1279_, lean_object* v_sep_1280_, lean_object* v_allowTrailingSep_1281_, lean_object* v_iniSz_1282_, lean_object* v_pOpt_1283_, lean_object* v_c_1284_, lean_object* v_s_1285_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1286_; uint8_t v_pOpt_boxed_1287_; lean_object* v_res_1288_; 
v_allowTrailingSep_boxed_1286_ = lean_unbox(v_allowTrailingSep_1281_);
v_pOpt_boxed_1287_ = lean_unbox(v_pOpt_1283_);
v_res_1288_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1279_, v_sep_1280_, v_allowTrailingSep_boxed_1286_, v_iniSz_1282_, v_pOpt_boxed_1287_, v_c_1284_, v_s_1285_);
lean_dec(v_iniSz_1282_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1289_, lean_object* v_sep_1290_, uint8_t v_allowTrailingSep_1291_, lean_object* v_iniSz_1292_, uint8_t v_pOpt_1293_, lean_object* v_c_1294_, lean_object* v_s_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1289_, v_sep_1290_, v_allowTrailingSep_1291_, v_iniSz_1292_, v_pOpt_1293_, v_c_1294_, v_s_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1297_, lean_object* v_sep_1298_, lean_object* v_allowTrailingSep_1299_, lean_object* v_iniSz_1300_, lean_object* v_pOpt_1301_, lean_object* v_c_1302_, lean_object* v_s_1303_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1304_; uint8_t v_pOpt_boxed_1305_; lean_object* v_res_1306_; 
v_allowTrailingSep_boxed_1304_ = lean_unbox(v_allowTrailingSep_1299_);
v_pOpt_boxed_1305_ = lean_unbox(v_pOpt_1301_);
v_res_1306_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1297_, v_sep_1298_, v_allowTrailingSep_boxed_1304_, v_iniSz_1300_, v_pOpt_boxed_1305_, v_c_1302_, v_s_1303_);
lean_dec(v_iniSz_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1307_, lean_object* v_p_1308_, lean_object* v_sep_1309_, lean_object* v_c_1310_, lean_object* v_s_1311_){
_start:
{
lean_object* v_iniSz_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; 
v_iniSz_1312_ = l_Lean_Parser_ParserState_stackSize(v_s_1311_);
v___x_1313_ = 1;
v___x_1314_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1308_, v_sep_1309_, v_allowTrailingSep_1307_, v_iniSz_1312_, v___x_1313_, v_c_1310_, v_s_1311_);
lean_dec(v_iniSz_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1315_, lean_object* v_p_1316_, lean_object* v_sep_1317_, lean_object* v_c_1318_, lean_object* v_s_1319_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1320_; lean_object* v_res_1321_; 
v_allowTrailingSep_boxed_1320_ = lean_unbox(v_allowTrailingSep_1315_);
v_res_1321_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1320_, v_p_1316_, v_sep_1317_, v_c_1318_, v_s_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1322_, lean_object* v_p_1323_, lean_object* v_sep_1324_, lean_object* v_c_1325_, lean_object* v_s_1326_){
_start:
{
lean_object* v_iniSz_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; 
v_iniSz_1327_ = l_Lean_Parser_ParserState_stackSize(v_s_1326_);
v___x_1328_ = 0;
v___x_1329_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1323_, v_sep_1324_, v_allowTrailingSep_1322_, v_iniSz_1327_, v___x_1328_, v_c_1325_, v_s_1326_);
lean_dec(v_iniSz_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1330_, lean_object* v_p_1331_, lean_object* v_sep_1332_, lean_object* v_c_1333_, lean_object* v_s_1334_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1335_; lean_object* v_res_1336_; 
v_allowTrailingSep_boxed_1335_ = lean_unbox(v_allowTrailingSep_1330_);
v_res_1336_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1335_, v_p_1331_, v_sep_1332_, v_c_1333_, v_s_1334_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1337_, lean_object* v_sep_1338_){
_start:
{
lean_object* v_collectTokens_1339_; lean_object* v_collectKinds_1340_; lean_object* v_collectTokens_1341_; lean_object* v_collectKinds_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_collectTokens_1339_ = lean_ctor_get(v_p_1337_, 0);
lean_inc_ref(v_collectTokens_1339_);
v_collectKinds_1340_ = lean_ctor_get(v_p_1337_, 1);
lean_inc_ref(v_collectKinds_1340_);
lean_dec_ref(v_p_1337_);
v_collectTokens_1341_ = lean_ctor_get(v_sep_1338_, 0);
v_collectKinds_1342_ = lean_ctor_get(v_sep_1338_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_sep_1338_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_sep_1338_, 2);
lean_dec(v_unused_1353_);
v___x_1344_ = v_sep_1338_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_collectKinds_1342_);
lean_inc(v_collectTokens_1341_);
lean_dec(v_sep_1338_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___f_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1346_, 0, v_collectKinds_1342_);
lean_closure_set(v___f_1346_, 1, v_collectKinds_1340_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1347_, 0, v_collectTokens_1341_);
lean_closure_set(v___f_1347_, 1, v_collectTokens_1339_);
v___x_1348_ = lean_box(1);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 2, v___x_1348_);
lean_ctor_set(v___x_1344_, 1, v___f_1346_);
lean_ctor_set(v___x_1344_, 0, v___f_1347_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___f_1347_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___f_1346_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1354_, lean_object* v_sep_1355_){
_start:
{
lean_object* v_collectTokens_1356_; lean_object* v_collectKinds_1357_; lean_object* v_firstTokens_1358_; lean_object* v_collectTokens_1359_; lean_object* v_collectKinds_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1369_; 
v_collectTokens_1356_ = lean_ctor_get(v_p_1354_, 0);
lean_inc_ref(v_collectTokens_1356_);
v_collectKinds_1357_ = lean_ctor_get(v_p_1354_, 1);
lean_inc_ref(v_collectKinds_1357_);
v_firstTokens_1358_ = lean_ctor_get(v_p_1354_, 2);
lean_inc(v_firstTokens_1358_);
lean_dec_ref(v_p_1354_);
v_collectTokens_1359_ = lean_ctor_get(v_sep_1355_, 0);
v_collectKinds_1360_ = lean_ctor_get(v_sep_1355_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_sep_1355_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v_sep_1355_, 2);
lean_dec(v_unused_1370_);
v___x_1362_ = v_sep_1355_;
v_isShared_1363_ = v_isSharedCheck_1369_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_collectKinds_1360_);
lean_inc(v_collectTokens_1359_);
lean_dec(v_sep_1355_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1369_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___x_1367_; 
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1364_, 0, v_collectKinds_1360_);
lean_closure_set(v___f_1364_, 1, v_collectKinds_1357_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1365_, 0, v_collectTokens_1359_);
lean_closure_set(v___f_1365_, 1, v_collectTokens_1356_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 2, v_firstTokens_1358_);
lean_ctor_set(v___x_1362_, 1, v___f_1364_);
lean_ctor_set(v___x_1362_, 0, v___f_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___f_1365_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___f_1364_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_firstTokens_1358_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1371_, lean_object* v_sep_1372_, uint8_t v_allowTrailingSep_1373_){
_start:
{
lean_object* v_info_1374_; lean_object* v_fn_1375_; lean_object* v_info_1376_; lean_object* v_fn_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1387_; 
v_info_1374_ = lean_ctor_get(v_p_1371_, 0);
lean_inc_ref(v_info_1374_);
v_fn_1375_ = lean_ctor_get(v_p_1371_, 1);
lean_inc_ref(v_fn_1375_);
lean_dec_ref(v_p_1371_);
v_info_1376_ = lean_ctor_get(v_sep_1372_, 0);
v_fn_1377_ = lean_ctor_get(v_sep_1372_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_sep_1372_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1379_ = v_sep_1372_;
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_fn_1377_);
lean_inc(v_info_1376_);
lean_dec(v_sep_1372_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1381_ = l_Lean_Parser_sepByInfo(v_info_1374_, v_info_1376_);
v___x_1382_ = lean_box(v_allowTrailingSep_1373_);
v___x_1383_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1383_, 0, v___x_1382_);
lean_closure_set(v___x_1383_, 1, v_fn_1375_);
lean_closure_set(v___x_1383_, 2, v_fn_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___x_1383_);
lean_ctor_set(v___x_1379_, 0, v___x_1381_);
v___x_1385_ = v___x_1379_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1388_, lean_object* v_sep_1389_, lean_object* v_allowTrailingSep_1390_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1391_; lean_object* v_res_1392_; 
v_allowTrailingSep_boxed_1391_ = lean_unbox(v_allowTrailingSep_1390_);
v_res_1392_ = l_Lean_Parser_sepByNoAntiquot(v_p_1388_, v_sep_1389_, v_allowTrailingSep_boxed_1391_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1393_, lean_object* v_sep_1394_, uint8_t v_allowTrailingSep_1395_){
_start:
{
lean_object* v_info_1396_; lean_object* v_fn_1397_; lean_object* v_info_1398_; lean_object* v_fn_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1409_; 
v_info_1396_ = lean_ctor_get(v_p_1393_, 0);
lean_inc_ref(v_info_1396_);
v_fn_1397_ = lean_ctor_get(v_p_1393_, 1);
lean_inc_ref(v_fn_1397_);
lean_dec_ref(v_p_1393_);
v_info_1398_ = lean_ctor_get(v_sep_1394_, 0);
v_fn_1399_ = lean_ctor_get(v_sep_1394_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_sep_1394_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1401_ = v_sep_1394_;
v_isShared_1402_ = v_isSharedCheck_1409_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_fn_1399_);
lean_inc(v_info_1398_);
lean_dec(v_sep_1394_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1409_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1403_ = l_Lean_Parser_sepBy1Info(v_info_1396_, v_info_1398_);
v___x_1404_ = lean_box(v_allowTrailingSep_1395_);
v___x_1405_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1405_, 0, v___x_1404_);
lean_closure_set(v___x_1405_, 1, v_fn_1397_);
lean_closure_set(v___x_1405_, 2, v_fn_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v___x_1405_);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1410_, lean_object* v_sep_1411_, lean_object* v_allowTrailingSep_1412_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1413_; lean_object* v_res_1414_; 
v_allowTrailingSep_boxed_1413_ = lean_unbox(v_allowTrailingSep_1412_);
v_res_1414_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1410_, v_sep_1411_, v_allowTrailingSep_boxed_1413_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1415_, lean_object* v_f_1416_, lean_object* v_c_1417_, lean_object* v_s_1418_){
_start:
{
lean_object* v_s_1419_; lean_object* v_stxStack_1420_; lean_object* v_errorMsg_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; uint8_t v___x_1424_; 
v_s_1419_ = lean_apply_2(v_p_1415_, v_c_1417_, v_s_1418_);
v_stxStack_1420_ = lean_ctor_get(v_s_1419_, 0);
lean_inc_ref(v_stxStack_1420_);
v_errorMsg_1421_ = lean_ctor_get(v_s_1419_, 4);
lean_inc(v_errorMsg_1421_);
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1421_, v___x_1422_);
v___x_1424_ = lean_bool_not(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v_stx_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_stx_1425_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1420_);
lean_dec_ref(v_stxStack_1420_);
v___x_1426_ = l_Lean_Parser_ParserState_popSyntax(v_s_1419_);
v___x_1427_ = lean_apply_1(v_f_1416_, v_stx_1425_);
v___x_1428_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1426_, v___x_1427_);
return v___x_1428_;
}
else
{
lean_dec_ref(v_stxStack_1420_);
lean_dec_ref(v_f_1416_);
return v_s_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1429_){
_start:
{
lean_object* v_collectTokens_1430_; lean_object* v_collectKinds_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_collectTokens_1430_ = lean_ctor_get(v_p_1429_, 0);
v_collectKinds_1431_ = lean_ctor_get(v_p_1429_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_p_1429_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_p_1429_, 2);
lean_dec(v_unused_1440_);
v___x_1433_ = v_p_1429_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_collectKinds_1431_);
lean_inc(v_collectTokens_1430_);
lean_dec(v_p_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_box(1);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 2, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_collectTokens_1430_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_collectKinds_1431_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1441_, lean_object* v_f_1442_){
_start:
{
lean_object* v_info_1443_; lean_object* v_fn_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1453_; 
v_info_1443_ = lean_ctor_get(v_p_1441_, 0);
v_fn_1444_ = lean_ctor_get(v_p_1441_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_p_1441_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1446_ = v_p_1441_;
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_fn_1444_);
lean_inc(v_info_1443_);
lean_dec(v_p_1441_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1448_ = l_Lean_Parser_withResultOfInfo(v_info_1443_);
v___x_1449_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1449_, 0, v_fn_1444_);
lean_closure_set(v___x_1449_, 1, v_f_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1449_);
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1451_ = v___x_1446_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = l_Lean_Syntax_getNumArgs(v_stx_1454_);
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_dec_eq(v___x_1455_, v___x_1456_);
lean_dec(v___x_1455_);
if (v___x_1457_ == 0)
{
lean_inc(v_stx_1454_);
return v_stx_1454_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_Lean_Syntax_getArg(v_stx_1454_, v___x_1458_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1460_);
lean_dec(v_stx_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___f_1464_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1465_ = l_Lean_Parser_many1NoAntiquot(v_p_1463_);
v___x_1466_ = l_Lean_Parser_withResultOf(v___x_1465_, v___f_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1467_, lean_object* v_errorMsg_1468_, lean_object* v_c_1469_, lean_object* v_s_1470_){
_start:
{
lean_object* v_pos_1471_; lean_object* v_toInputContext_1472_; uint8_t v___x_1473_; 
v_pos_1471_ = lean_ctor_get(v_s_1470_, 2);
v_toInputContext_1472_ = lean_ctor_get(v_c_1469_, 0);
v___x_1473_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1472_, v_pos_1471_);
if (v___x_1473_ == 0)
{
lean_object* v_inputString_1474_; uint32_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_inputString_1474_ = lean_ctor_get(v_toInputContext_1472_, 0);
v___x_1475_ = lean_string_utf8_get_fast(v_inputString_1474_, v_pos_1471_);
v___x_1476_ = lean_box_uint32(v___x_1475_);
v___x_1477_ = lean_apply_1(v_p_1467_, v___x_1476_);
v___x_1478_ = lean_unbox(v___x_1477_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = 1;
v___x_1480_ = lean_box(0);
v___x_1481_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1470_, v_errorMsg_1468_, v___x_1480_, v___x_1479_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; 
lean_inc(v_pos_1471_);
lean_dec_ref(v_errorMsg_1468_);
v___x_1482_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1470_, v_c_1469_, v_pos_1471_);
lean_dec(v_pos_1471_);
return v___x_1482_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v_errorMsg_1468_);
lean_dec_ref(v_p_1467_);
v___x_1483_ = lean_box(0);
v___x_1484_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1470_, v___x_1483_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1485_, lean_object* v_errorMsg_1486_, lean_object* v_c_1487_, lean_object* v_s_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Parser_satisfyFn(v_p_1485_, v_errorMsg_1486_, v_c_1487_, v_s_1488_);
lean_dec_ref(v_c_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1490_, lean_object* v_c_1491_, lean_object* v_s_1492_){
_start:
{
lean_object* v_pos_1493_; lean_object* v_toInputContext_1494_; uint8_t v___x_1495_; 
v_pos_1493_ = lean_ctor_get(v_s_1492_, 2);
v_toInputContext_1494_ = lean_ctor_get(v_c_1491_, 0);
v___x_1495_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1494_, v_pos_1493_);
if (v___x_1495_ == 0)
{
lean_object* v_inputString_1496_; uint32_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_inputString_1496_ = lean_ctor_get(v_toInputContext_1494_, 0);
v___x_1497_ = lean_string_utf8_get_fast(v_inputString_1496_, v_pos_1493_);
v___x_1498_ = lean_box_uint32(v___x_1497_);
lean_inc_ref(v_p_1490_);
v___x_1499_ = lean_apply_1(v_p_1490_, v___x_1498_);
v___x_1500_ = lean_unbox(v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_inc(v_pos_1493_);
v___x_1501_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1492_, v_c_1491_, v_pos_1493_);
lean_dec(v_pos_1493_);
v_s_1492_ = v___x_1501_;
goto _start;
}
else
{
lean_dec_ref(v_p_1490_);
return v_s_1492_;
}
}
else
{
lean_dec_ref(v_p_1490_);
return v_s_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1503_, lean_object* v_c_1504_, lean_object* v_s_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Parser_takeUntilFn(v_p_1503_, v_c_1504_, v_s_1505_);
lean_dec_ref(v_c_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1507_, uint32_t v_c_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1509_ = lean_box_uint32(v_c_1508_);
v___x_1510_ = lean_apply_1(v_p_1507_, v___x_1509_);
v___x_1511_ = lean_unbox(v___x_1510_);
v___x_1512_ = lean_bool_not(v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1513_, lean_object* v_c_1514_){
_start:
{
uint32_t v_c_boxed_1515_; uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_c_boxed_1515_ = lean_unbox_uint32(v_c_1514_);
lean_dec(v_c_1514_);
v_res_1516_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1513_, v_c_boxed_1515_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___f_1521_; lean_object* v___x_1522_; 
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1521_, 0, v_p_1518_);
v___x_1522_ = l_Lean_Parser_takeUntilFn(v___f_1521_, v_a_1519_, v_a_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Parser_takeWhileFn(v_p_1523_, v_a_1524_, v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1527_, lean_object* v_errorMsg_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc_ref(v_p_1527_);
v___x_1531_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1531_, 0, v_p_1527_);
lean_closure_set(v___x_1531_, 1, v_errorMsg_1528_);
v___x_1532_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1532_, 0, v_p_1527_);
v___x_1533_ = l_Lean_Parser_andthenFn(v___x_1531_, v___x_1532_, v_a_1529_, v_a_1530_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1535_, lean_object* v_s_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1538_ = lean_box(0);
v___x_1539_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1536_, v___x_1537_, v___x_1538_, v_pushMissingOnError_1535_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1540_, lean_object* v_s_1541_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1542_; lean_object* v_res_1543_; 
v_pushMissingOnError_boxed_1542_ = lean_unbox(v_pushMissingOnError_1540_);
v_res_1543_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1542_, v_s_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1544_, lean_object* v_nesting_1545_, lean_object* v_c_1546_, lean_object* v_s_1547_){
_start:
{
lean_object* v_pos_1548_; lean_object* v_toInputContext_1549_; uint8_t v___x_1550_; 
v_pos_1548_ = lean_ctor_get(v_s_1547_, 2);
v_toInputContext_1549_ = lean_ctor_get(v_c_1546_, 0);
v___x_1550_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1549_, v_pos_1548_);
if (v___x_1550_ == 0)
{
lean_object* v_inputString_1551_; uint32_t v_curr_1552_; lean_object* v_i_1553_; uint32_t v___x_1554_; uint8_t v___x_1555_; 
v_inputString_1551_ = lean_ctor_get(v_toInputContext_1549_, 0);
v_curr_1552_ = lean_string_utf8_get_fast(v_inputString_1551_, v_pos_1548_);
v_i_1553_ = lean_string_utf8_next_fast(v_inputString_1551_, v_pos_1548_);
v___x_1554_ = 45;
v___x_1555_ = lean_uint32_dec_eq(v_curr_1552_, v___x_1554_);
if (v___x_1555_ == 0)
{
uint32_t v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = 47;
v___x_1557_ = lean_uint32_dec_eq(v_curr_1552_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Parser_ParserState_setPos(v_s_1547_, v_i_1553_);
v_s_1547_ = v___x_1558_;
goto _start;
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1549_, v_i_1553_);
if (v___x_1560_ == 0)
{
uint32_t v_curr_1561_; uint8_t v___x_1562_; 
v_curr_1561_ = lean_string_utf8_get_fast(v_inputString_1551_, v_i_1553_);
v___x_1562_ = lean_uint32_dec_eq(v_curr_1561_, v___x_1554_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Parser_ParserState_setPos(v_s_1547_, v_i_1553_);
v_s_1547_ = v___x_1563_;
goto _start;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_nesting_1545_, v___x_1565_);
lean_dec(v_nesting_1545_);
v___x_1567_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1547_, v_c_1546_, v_i_1553_);
v_nesting_1545_ = v___x_1566_;
v_s_1547_ = v___x_1567_;
goto _start;
}
}
else
{
lean_object* v___x_1569_; 
lean_dec(v_nesting_1545_);
v___x_1569_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1544_, v_s_1547_);
return v___x_1569_;
}
}
}
else
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1549_, v_i_1553_);
if (v___x_1570_ == 0)
{
uint32_t v_curr_1571_; uint32_t v___x_1572_; uint8_t v___x_1573_; 
v_curr_1571_ = lean_string_utf8_get_fast(v_inputString_1551_, v_i_1553_);
v___x_1572_ = 47;
v___x_1573_ = lean_uint32_dec_eq(v_curr_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Parser_ParserState_setPos(v_s_1547_, v_i_1553_);
v_s_1547_ = v___x_1574_;
goto _start;
}
else
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_dec_eq(v_nesting_1545_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_nat_sub(v_nesting_1545_, v___x_1576_);
lean_dec(v_nesting_1545_);
v___x_1579_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1547_, v_c_1546_, v_i_1553_);
v_nesting_1545_ = v___x_1578_;
v_s_1547_ = v___x_1579_;
goto _start;
}
else
{
lean_object* v___x_1581_; 
lean_dec(v_nesting_1545_);
v___x_1581_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1547_, v_c_1546_, v_i_1553_);
return v___x_1581_;
}
}
}
else
{
lean_object* v___x_1582_; 
lean_dec(v_nesting_1545_);
v___x_1582_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1544_, v_s_1547_);
return v___x_1582_;
}
}
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_nesting_1545_);
v___x_1583_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1544_, v_s_1547_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1584_, lean_object* v_nesting_1585_, lean_object* v_c_1586_, lean_object* v_s_1587_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1588_; lean_object* v_res_1589_; 
v_pushMissingOnError_boxed_1588_ = lean_unbox(v_pushMissingOnError_1584_);
v_res_1589_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1588_, v_nesting_1585_, v_c_1586_, v_s_1587_);
lean_dec_ref(v_c_1586_);
return v_res_1589_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1590_){
_start:
{
uint32_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = 10;
v___x_1592_ = lean_uint32_dec_eq(v_c_1590_, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1593_){
_start:
{
uint32_t v_c_boxed_1594_; uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_c_boxed_1594_ = lean_unbox_uint32(v_c_1593_);
lean_dec(v_c_1593_);
v_res_1595_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1594_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1602_, lean_object* v_s_1603_){
_start:
{
lean_object* v_pos_1604_; lean_object* v_toInputContext_1608_; uint8_t v___x_1609_; 
v_pos_1604_ = lean_ctor_get(v_s_1603_, 2);
v_toInputContext_1608_ = lean_ctor_get(v_c_1602_, 0);
v___x_1609_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1608_, v_pos_1604_);
if (v___x_1609_ == 0)
{
lean_object* v_inputString_1610_; uint32_t v_curr_1611_; uint32_t v___x_1612_; uint8_t v___x_1613_; 
v_inputString_1610_ = lean_ctor_get(v_toInputContext_1608_, 0);
v_curr_1611_ = lean_string_utf8_get_fast(v_inputString_1610_, v_pos_1604_);
v___x_1612_ = 9;
v___x_1613_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
uint32_t v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = 13;
v___x_1615_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1614_);
if (v___x_1615_ == 0)
{
uint8_t v___y_1617_; uint8_t v___y_1644_; uint32_t v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = 32;
v___x_1648_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1647_);
if (v___x_1648_ == 0)
{
v___y_1644_ = v___x_1613_;
goto v___jp_1643_;
}
else
{
v___y_1644_ = v___x_1648_;
goto v___jp_1643_;
}
v___jp_1616_:
{
if (v___y_1617_ == 0)
{
uint32_t v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = 45;
v___x_1619_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1618_);
if (v___x_1619_ == 0)
{
uint32_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 47;
v___x_1621_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec_ref(v_c_1602_);
return v_s_1603_;
}
else
{
lean_object* v_i_1622_; uint32_t v_curr_1623_; uint8_t v___x_1624_; 
v_i_1622_ = lean_string_utf8_next_fast(v_inputString_1610_, v_pos_1604_);
v_curr_1623_ = lean_string_utf8_get(v_inputString_1610_, v_i_1622_);
v___x_1624_ = lean_uint32_dec_eq(v_curr_1623_, v___x_1618_);
if (v___x_1624_ == 0)
{
lean_dec_ref(v_c_1602_);
return v_s_1603_;
}
else
{
lean_object* v_i_1625_; uint32_t v_curr_1626_; uint8_t v___x_1627_; 
v_i_1625_ = lean_string_utf8_next(v_inputString_1610_, v_i_1622_);
v_curr_1626_ = lean_string_utf8_get(v_inputString_1610_, v_i_1625_);
v___x_1627_ = lean_uint32_dec_eq(v_curr_1626_, v___x_1618_);
if (v___x_1627_ == 0)
{
uint32_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = 33;
v___x_1629_ = lean_uint32_dec_eq(v_curr_1626_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_box(v___x_1629_);
v___x_1632_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1632_, 0, v___x_1631_);
lean_closure_set(v___x_1632_, 1, v___x_1630_);
v___x_1633_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1634_ = l_Lean_Parser_ParserState_next(v_s_1603_, v_c_1602_, v_i_1625_);
lean_dec(v_i_1625_);
v___x_1635_ = l_Lean_Parser_andthenFn(v___x_1632_, v___x_1633_, v_c_1602_, v___x_1634_);
return v___x_1635_;
}
else
{
lean_dec(v_i_1625_);
lean_dec_ref(v_c_1602_);
return v_s_1603_;
}
}
else
{
lean_dec(v_i_1625_);
lean_dec_ref(v_c_1602_);
return v_s_1603_;
}
}
}
}
else
{
lean_object* v_i_1636_; uint32_t v_curr_1637_; uint8_t v___x_1638_; 
v_i_1636_ = lean_string_utf8_next_fast(v_inputString_1610_, v_pos_1604_);
v_curr_1637_ = lean_string_utf8_get(v_inputString_1610_, v_i_1636_);
v___x_1638_ = lean_uint32_dec_eq(v_curr_1637_, v___x_1618_);
if (v___x_1638_ == 0)
{
lean_dec_ref(v_c_1602_);
return v_s_1603_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1640_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1641_ = l_Lean_Parser_ParserState_next(v_s_1603_, v_c_1602_, v_i_1636_);
v___x_1642_ = l_Lean_Parser_andthenFn(v___x_1639_, v___x_1640_, v_c_1602_, v___x_1641_);
return v___x_1642_;
}
}
}
else
{
lean_inc(v_pos_1604_);
goto v___jp_1605_;
}
}
v___jp_1643_:
{
if (v___y_1644_ == 0)
{
if (v___x_1615_ == 0)
{
uint32_t v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = 10;
v___x_1646_ = lean_uint32_dec_eq(v_curr_1611_, v___x_1645_);
v___y_1617_ = v___x_1646_;
goto v___jp_1616_;
}
else
{
v___y_1617_ = v___x_1615_;
goto v___jp_1616_;
}
}
else
{
lean_inc(v_pos_1604_);
goto v___jp_1605_;
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec_ref(v_c_1602_);
v___x_1649_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1603_, v___x_1649_, v___x_1650_, v___x_1613_);
return v___x_1651_;
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v_c_1602_);
v___x_1652_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1603_, v___x_1652_, v___x_1653_, v___x_1609_);
return v___x_1654_;
}
}
else
{
lean_dec_ref(v_c_1602_);
return v_s_1603_;
}
v___jp_1605_:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1603_, v_c_1602_, v_pos_1604_);
lean_dec(v_pos_1604_);
v_s_1603_ = v___x_1606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1655_, lean_object* v_p_1656_){
_start:
{
lean_object* v_toInputContext_1657_; lean_object* v_inputString_1658_; lean_object* v_endPos_1659_; uint8_t v___x_1660_; 
v_toInputContext_1657_ = lean_ctor_get(v_c_1655_, 0);
v_inputString_1658_ = lean_ctor_get(v_toInputContext_1657_, 0);
v_endPos_1659_ = lean_ctor_get(v_toInputContext_1657_, 3);
v___x_1660_ = lean_nat_dec_le(v_p_1656_, v_endPos_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_inc(v_endPos_1659_);
lean_inc_ref(v_inputString_1658_);
v___x_1661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1661_, 0, v_inputString_1658_);
lean_ctor_set(v___x_1661_, 1, v_p_1656_);
lean_ctor_set(v___x_1661_, 2, v_endPos_1659_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; 
lean_inc(v_p_1656_);
lean_inc_ref(v_inputString_1658_);
v___x_1662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1662_, 0, v_inputString_1658_);
lean_ctor_set(v___x_1662_, 1, v_p_1656_);
lean_ctor_set(v___x_1662_, 2, v_p_1656_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1663_, lean_object* v_p_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1663_, v_p_1664_);
lean_dec_ref(v_c_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1666_, uint8_t v_trailingWs_1667_, lean_object* v_c_1668_, lean_object* v_s_1669_){
_start:
{
lean_object* v_toInputContext_1670_; lean_object* v_pos_1671_; lean_object* v_inputString_1672_; lean_object* v_endPos_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1701_; 
v_toInputContext_1670_ = lean_ctor_get(v_c_1668_, 0);
lean_inc_ref(v_toInputContext_1670_);
v_pos_1671_ = lean_ctor_get(v_s_1669_, 2);
v_inputString_1672_ = lean_ctor_get(v_toInputContext_1670_, 0);
v_endPos_1673_ = lean_ctor_get(v_toInputContext_1670_, 3);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_toInputContext_1670_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1702_ = lean_ctor_get(v_toInputContext_1670_, 2);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_toInputContext_1670_, 1);
lean_dec(v_unused_1703_);
v___x_1675_ = v_toInputContext_1670_;
v_isShared_1676_ = v_isSharedCheck_1701_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_endPos_1673_);
lean_inc(v_inputString_1672_);
lean_dec(v_toInputContext_1670_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1701_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_leading_1677_; lean_object* v_val_1678_; 
lean_inc(v_startPos_1666_);
v_leading_1677_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1668_, v_startPos_1666_);
v_val_1678_ = lean_string_utf8_extract(v_inputString_1672_, v_startPos_1666_, v_pos_1671_);
if (v_trailingWs_1667_ == 0)
{
lean_object* v_trailing_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_dec(v_endPos_1673_);
lean_dec_ref(v_inputString_1672_);
lean_inc(v_pos_1671_);
v_trailing_1679_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1668_, v_pos_1671_);
lean_dec_ref(v_c_1668_);
v___x_1680_ = lean_string_utf8_byte_size(v_val_1678_);
v___x_1681_ = lean_nat_add(v_startPos_1666_, v___x_1680_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v___x_1681_);
lean_ctor_set(v___x_1675_, 2, v_trailing_1679_);
lean_ctor_set(v___x_1675_, 1, v_startPos_1666_);
lean_ctor_set(v___x_1675_, 0, v_leading_1677_);
v___x_1683_ = v___x_1675_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_leading_1677_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_startPos_1666_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_trailing_1679_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v_atom_1684_; lean_object* v___x_1685_; 
v_atom_1684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1684_, 0, v___x_1683_);
lean_ctor_set(v_atom_1684_, 1, v_val_1678_);
v___x_1685_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1669_, v_atom_1684_);
return v___x_1685_;
}
}
else
{
lean_object* v_s_1687_; lean_object* v___y_1689_; lean_object* v_pos_1697_; uint8_t v___x_1698_; 
lean_inc(v_pos_1671_);
v_s_1687_ = l_Lean_Parser_whitespace(v_c_1668_, v_s_1669_);
v_pos_1697_ = lean_ctor_get(v_s_1687_, 2);
lean_inc(v_pos_1697_);
v___x_1698_ = lean_nat_dec_le(v_pos_1697_, v_endPos_1673_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
lean_dec(v_pos_1697_);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v_inputString_1672_);
lean_ctor_set(v___x_1699_, 1, v_pos_1671_);
lean_ctor_set(v___x_1699_, 2, v_endPos_1673_);
v___y_1689_ = v___x_1699_;
goto v___jp_1688_;
}
else
{
lean_object* v___x_1700_; 
lean_dec(v_endPos_1673_);
v___x_1700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1700_, 0, v_inputString_1672_);
lean_ctor_set(v___x_1700_, 1, v_pos_1671_);
lean_ctor_set(v___x_1700_, 2, v_pos_1697_);
v___y_1689_ = v___x_1700_;
goto v___jp_1688_;
}
v___jp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1690_ = lean_string_utf8_byte_size(v_val_1678_);
v___x_1691_ = lean_nat_add(v_startPos_1666_, v___x_1690_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v___x_1691_);
lean_ctor_set(v___x_1675_, 2, v___y_1689_);
lean_ctor_set(v___x_1675_, 1, v_startPos_1666_);
lean_ctor_set(v___x_1675_, 0, v_leading_1677_);
v___x_1693_ = v___x_1675_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_leading_1677_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_startPos_1666_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v___y_1689_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v_atom_1694_; lean_object* v___x_1695_; 
v_atom_1694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1694_, 0, v___x_1693_);
lean_ctor_set(v_atom_1694_, 1, v_val_1678_);
v___x_1695_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1687_, v_atom_1694_);
return v___x_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1704_, lean_object* v_trailingWs_1705_, lean_object* v_c_1706_, lean_object* v_s_1707_){
_start:
{
uint8_t v_trailingWs_boxed_1708_; lean_object* v_res_1709_; 
v_trailingWs_boxed_1708_ = lean_unbox(v_trailingWs_1705_);
v_res_1709_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1704_, v_trailingWs_boxed_1708_, v_c_1706_, v_s_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1710_, uint8_t v_trailingWs_1711_, lean_object* v_c_1712_, lean_object* v_s_1713_){
_start:
{
lean_object* v_pos_1714_; lean_object* v_s_1715_; lean_object* v_errorMsg_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; 
v_pos_1714_ = lean_ctor_get(v_s_1713_, 2);
lean_inc(v_pos_1714_);
lean_inc_ref(v_c_1712_);
v_s_1715_ = lean_apply_2(v_p_1710_, v_c_1712_, v_s_1713_);
v_errorMsg_1716_ = lean_ctor_get(v_s_1715_, 4);
lean_inc(v_errorMsg_1716_);
v___x_1717_ = lean_box(0);
v___x_1718_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1716_, v___x_1717_);
v___x_1719_ = lean_bool_not(v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1714_, v_trailingWs_1711_, v_c_1712_, v_s_1715_);
return v___x_1720_;
}
else
{
lean_dec(v_pos_1714_);
lean_dec_ref(v_c_1712_);
return v_s_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1721_, lean_object* v_trailingWs_1722_, lean_object* v_c_1723_, lean_object* v_s_1724_){
_start:
{
uint8_t v_trailingWs_boxed_1725_; lean_object* v_res_1726_; 
v_trailingWs_boxed_1725_ = lean_unbox(v_trailingWs_1722_);
v_res_1726_ = l_Lean_Parser_rawFn(v_p_1721_, v_trailingWs_boxed_1725_, v_c_1723_, v_s_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1727_, uint32_t v_d_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_uint32_dec_eq(v_c_1727_, v_d_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1730_, lean_object* v_d_1731_){
_start:
{
uint32_t v_c_boxed_1732_; uint32_t v_d_boxed_1733_; uint8_t v_res_1734_; lean_object* v_r_1735_; 
v_c_boxed_1732_ = lean_unbox_uint32(v_c_1730_);
lean_dec(v_c_1730_);
v_d_boxed_1733_ = lean_unbox_uint32(v_d_1731_);
lean_dec(v_d_1731_);
v_res_1734_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1732_, v_d_boxed_1733_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1738_, uint8_t v_trailingWs_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1742_ = lean_box_uint32(v_c_1738_);
v___f_1743_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1743_, 0, v___x_1742_);
v___x_1744_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1745_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1746_ = lean_string_push(v___x_1745_, v_c_1738_);
v___x_1747_ = lean_string_append(v___x_1744_, v___x_1746_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_string_append(v___x_1747_, v___x_1744_);
v___x_1749_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1749_, 0, v___f_1743_);
lean_closure_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_Parser_rawFn(v___x_1749_, v_trailingWs_1739_, v_a_1740_, v_a_1741_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1751_, lean_object* v_trailingWs_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
uint32_t v_c_boxed_1755_; uint8_t v_trailingWs_boxed_1756_; lean_object* v_res_1757_; 
v_c_boxed_1755_ = lean_unbox_uint32(v_c_1751_);
lean_dec(v_c_1751_);
v_trailingWs_boxed_1756_ = lean_unbox(v_trailingWs_1752_);
v_res_1757_ = l_Lean_Parser_chFn(v_c_boxed_1755_, v_trailingWs_boxed_1756_, v_a_1753_, v_a_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1758_, uint8_t v_trailingWs_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1760_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1761_ = lean_box_uint32(v_c_1758_);
v___x_1762_ = lean_box(v_trailingWs_1759_);
v___x_1763_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1763_, 0, v___x_1761_);
lean_closure_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1760_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1765_, lean_object* v_trailingWs_1766_){
_start:
{
uint32_t v_c_boxed_1767_; uint8_t v_trailingWs_boxed_1768_; lean_object* v_res_1769_; 
v_c_boxed_1767_ = lean_unbox_uint32(v_c_1765_);
lean_dec(v_c_1765_);
v_trailingWs_boxed_1768_ = lean_unbox(v_trailingWs_1766_);
v_res_1769_ = l_Lean_Parser_rawCh(v_c_boxed_1767_, v_trailingWs_boxed_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1771_, lean_object* v_s_1772_){
_start:
{
lean_object* v_pos_1773_; lean_object* v_toInputContext_1774_; uint8_t v___x_1775_; 
v_pos_1773_ = lean_ctor_get(v_s_1772_, 2);
v_toInputContext_1774_ = lean_ctor_get(v_c_1771_, 0);
v___x_1775_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1774_, v_pos_1773_);
if (v___x_1775_ == 0)
{
lean_object* v_inputString_1776_; uint8_t v___x_1777_; uint32_t v_curr_1778_; lean_object* v_i_1779_; uint8_t v___y_1781_; uint8_t v___y_1787_; uint8_t v___y_1794_; uint32_t v___x_1800_; uint8_t v___x_1801_; 
v_inputString_1776_ = lean_ctor_get(v_toInputContext_1774_, 0);
v___x_1777_ = 1;
v_curr_1778_ = lean_string_utf8_get_fast(v_inputString_1776_, v_pos_1773_);
v_i_1779_ = lean_string_utf8_next_fast(v_inputString_1776_, v_pos_1773_);
v___x_1800_ = 48;
v___x_1801_ = lean_uint32_dec_le(v___x_1800_, v_curr_1778_);
if (v___x_1801_ == 0)
{
v___y_1794_ = v___x_1801_;
goto v___jp_1793_;
}
else
{
uint32_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = 57;
v___x_1803_ = lean_uint32_dec_le(v_curr_1778_, v___x_1802_);
v___y_1794_ = v___x_1803_;
goto v___jp_1793_;
}
v___jp_1780_:
{
if (v___y_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1772_, v___x_1782_, v___x_1783_, v___x_1777_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Parser_ParserState_setPos(v_s_1772_, v_i_1779_);
return v___x_1785_;
}
}
v___jp_1786_:
{
if (v___y_1787_ == 0)
{
uint32_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = 65;
v___x_1789_ = lean_uint32_dec_le(v___x_1788_, v_curr_1778_);
if (v___x_1789_ == 0)
{
v___y_1781_ = v___x_1789_;
goto v___jp_1780_;
}
else
{
uint32_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = 70;
v___x_1791_ = lean_uint32_dec_le(v_curr_1778_, v___x_1790_);
v___y_1781_ = v___x_1791_;
goto v___jp_1780_;
}
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Parser_ParserState_setPos(v_s_1772_, v_i_1779_);
return v___x_1792_;
}
}
v___jp_1793_:
{
if (v___y_1794_ == 0)
{
uint32_t v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = 97;
v___x_1796_ = lean_uint32_dec_le(v___x_1795_, v_curr_1778_);
if (v___x_1796_ == 0)
{
v___y_1787_ = v___x_1796_;
goto v___jp_1786_;
}
else
{
uint32_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = 102;
v___x_1798_ = lean_uint32_dec_le(v_curr_1778_, v___x_1797_);
v___y_1787_ = v___x_1798_;
goto v___jp_1786_;
}
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Parser_ParserState_setPos(v_s_1772_, v_i_1779_);
return v___x_1799_;
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_box(0);
v___x_1805_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1772_, v___x_1804_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1806_, lean_object* v_s_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Parser_hexDigitFn(v_c_1806_, v_s_1807_);
lean_dec_ref(v_c_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1811_, lean_object* v_c_1812_, lean_object* v_s_1813_){
_start:
{
lean_object* v_pos_1814_; lean_object* v_toInputContext_1818_; uint8_t v___x_1819_; 
v_pos_1814_ = lean_ctor_get(v_s_1813_, 2);
v_toInputContext_1818_ = lean_ctor_get(v_c_1812_, 0);
v___x_1819_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1818_, v_pos_1814_);
if (v___x_1819_ == 0)
{
lean_object* v_inputString_1820_; uint8_t v___x_1821_; uint8_t v___y_1823_; uint32_t v_curr_1827_; uint8_t v___y_1829_; uint32_t v___x_1834_; uint8_t v___x_1835_; 
v_inputString_1820_ = lean_ctor_get(v_toInputContext_1818_, 0);
v___x_1821_ = 1;
v_curr_1827_ = lean_string_utf8_get_fast(v_inputString_1820_, v_pos_1814_);
v___x_1834_ = 10;
v___x_1835_ = lean_uint32_dec_eq(v_curr_1827_, v___x_1834_);
if (v___x_1835_ == 0)
{
uint32_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = 32;
v___x_1837_ = lean_uint32_dec_eq(v_curr_1827_, v___x_1836_);
if (v___x_1837_ == 0)
{
uint32_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = 9;
v___x_1839_ = lean_uint32_dec_eq(v_curr_1827_, v___x_1838_);
v___y_1829_ = v___x_1839_;
goto v___jp_1828_;
}
else
{
v___y_1829_ = v___x_1837_;
goto v___jp_1828_;
}
}
else
{
if (v_seenNewline_1811_ == 0)
{
lean_object* v___x_1840_; 
lean_inc(v_pos_1814_);
v___x_1840_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1813_, v_c_1812_, v_pos_1814_);
lean_dec(v_pos_1814_);
v_seenNewline_1811_ = v___x_1821_;
v_s_1813_ = v___x_1840_;
goto _start;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1843_ = lean_box(0);
v___x_1844_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1813_, v___x_1842_, v___x_1843_, v___x_1821_);
return v___x_1844_;
}
}
v___jp_1822_:
{
if (v___y_1823_ == 0)
{
if (v_seenNewline_1811_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1825_ = lean_box(0);
v___x_1826_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1813_, v___x_1824_, v___x_1825_, v___x_1821_);
return v___x_1826_;
}
else
{
return v_s_1813_;
}
}
else
{
lean_inc(v_pos_1814_);
goto v___jp_1815_;
}
}
v___jp_1828_:
{
if (v___y_1829_ == 0)
{
uint32_t v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = 13;
v___x_1831_ = lean_uint32_dec_eq(v_curr_1827_, v___x_1830_);
if (v___x_1831_ == 0)
{
uint32_t v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = 10;
v___x_1833_ = lean_uint32_dec_eq(v_curr_1827_, v___x_1832_);
v___y_1823_ = v___x_1833_;
goto v___jp_1822_;
}
else
{
v___y_1823_ = v___x_1831_;
goto v___jp_1822_;
}
}
else
{
lean_inc(v_pos_1814_);
goto v___jp_1815_;
}
}
}
else
{
return v_s_1813_;
}
v___jp_1815_:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1813_, v_c_1812_, v_pos_1814_);
lean_dec(v_pos_1814_);
v_s_1813_ = v___x_1816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1845_, lean_object* v_c_1846_, lean_object* v_s_1847_){
_start:
{
uint8_t v_seenNewline_boxed_1848_; lean_object* v_res_1849_; 
v_seenNewline_boxed_1848_ = lean_unbox(v_seenNewline_1845_);
v_res_1849_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1848_, v_c_1846_, v_s_1847_);
lean_dec_ref(v_c_1846_);
return v_res_1849_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1851_);
v___x_1852_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1852_, 0, v___x_1851_);
lean_closure_set(v___x_1852_, 1, v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1854_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1855_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1855_, 0, v___x_1854_);
lean_closure_set(v___x_1855_, 1, v___x_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1856_, uint8_t v_inString_1857_, lean_object* v_c_1858_, lean_object* v_s_1859_){
_start:
{
lean_object* v_pos_1860_; lean_object* v_toInputContext_1861_; uint8_t v___x_1862_; 
v_pos_1860_ = lean_ctor_get(v_s_1859_, 2);
v_toInputContext_1861_ = lean_ctor_get(v_c_1858_, 0);
v___x_1862_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1861_, v_pos_1860_);
if (v___x_1862_ == 0)
{
lean_object* v_inputString_1863_; uint32_t v_curr_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_inputString_1863_ = lean_ctor_get(v_toInputContext_1861_, 0);
v_curr_1864_ = lean_string_utf8_get_fast(v_inputString_1863_, v_pos_1860_);
v___x_1865_ = lean_box_uint32(v_curr_1864_);
v___x_1866_ = lean_apply_1(v_isQuotable_1856_, v___x_1865_);
v___x_1867_ = lean_unbox(v___x_1866_);
if (v___x_1867_ == 0)
{
uint32_t v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = 120;
v___x_1869_ = lean_uint32_dec_eq(v_curr_1864_, v___x_1868_);
if (v___x_1869_ == 0)
{
uint32_t v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = 117;
v___x_1871_ = lean_uint32_dec_eq(v_curr_1864_, v___x_1870_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; 
v___x_1872_ = 1;
if (v_inString_1857_ == 0)
{
lean_dec_ref(v_c_1858_);
goto v___jp_1873_;
}
else
{
uint32_t v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = 10;
v___x_1878_ = lean_uint32_dec_eq(v_curr_1864_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_dec_ref(v_c_1858_);
goto v___jp_1873_;
}
else
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Parser_stringGapFn(v___x_1871_, v_c_1858_, v_s_1859_);
lean_dec_ref(v_c_1858_);
return v___x_1879_;
}
}
v___jp_1873_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1859_, v___x_1874_, v___x_1875_, v___x_1872_);
return v___x_1876_;
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_inc(v_pos_1860_);
v___x_1880_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1881_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1882_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1859_, v_c_1858_, v_pos_1860_);
lean_dec(v_pos_1860_);
v___x_1883_ = l_Lean_Parser_andthenFn(v___x_1880_, v___x_1881_, v_c_1858_, v___x_1882_);
return v___x_1883_;
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_inc(v_pos_1860_);
v___x_1884_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1885_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1859_, v_c_1858_, v_pos_1860_);
lean_dec(v_pos_1860_);
lean_inc_ref(v___x_1884_);
v___x_1886_ = l_Lean_Parser_andthenFn(v___x_1884_, v___x_1884_, v_c_1858_, v___x_1885_);
return v___x_1886_;
}
}
else
{
lean_object* v___x_1887_; 
lean_inc(v_pos_1860_);
v___x_1887_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1859_, v_c_1858_, v_pos_1860_);
lean_dec(v_pos_1860_);
lean_dec_ref(v_c_1858_);
return v___x_1887_;
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_c_1858_);
lean_dec_ref(v_isQuotable_1856_);
v___x_1888_ = lean_box(0);
v___x_1889_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1859_, v___x_1888_);
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1890_, lean_object* v_inString_1891_, lean_object* v_c_1892_, lean_object* v_s_1893_){
_start:
{
uint8_t v_inString_boxed_1894_; lean_object* v_res_1895_; 
v_inString_boxed_1894_ = lean_unbox(v_inString_1891_);
v_res_1895_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1890_, v_inString_boxed_1894_, v_c_1892_, v_s_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1896_){
_start:
{
uint8_t v___y_1898_; uint32_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = 92;
v___x_1908_ = lean_uint32_dec_eq(v_c_1896_, v___x_1907_);
if (v___x_1908_ == 0)
{
uint32_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = 34;
v___x_1910_ = lean_uint32_dec_eq(v_c_1896_, v___x_1909_);
v___y_1898_ = v___x_1910_;
goto v___jp_1897_;
}
else
{
v___y_1898_ = v___x_1908_;
goto v___jp_1897_;
}
v___jp_1897_:
{
if (v___y_1898_ == 0)
{
uint32_t v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = 39;
v___x_1900_ = lean_uint32_dec_eq(v_c_1896_, v___x_1899_);
if (v___x_1900_ == 0)
{
uint32_t v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = 114;
v___x_1902_ = lean_uint32_dec_eq(v_c_1896_, v___x_1901_);
if (v___x_1902_ == 0)
{
uint32_t v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = 110;
v___x_1904_ = lean_uint32_dec_eq(v_c_1896_, v___x_1903_);
if (v___x_1904_ == 0)
{
uint32_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = 116;
v___x_1906_ = lean_uint32_dec_eq(v_c_1896_, v___x_1905_);
return v___x_1906_;
}
else
{
return v___x_1904_;
}
}
else
{
return v___x_1902_;
}
}
else
{
return v___x_1900_;
}
}
else
{
return v___y_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1911_){
_start:
{
uint32_t v_c_boxed_1912_; uint8_t v_res_1913_; lean_object* v_r_1914_; 
v_c_boxed_1912_ = lean_unbox_uint32(v_c_1911_);
lean_dec(v_c_1911_);
v_res_1913_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1912_);
v_r_1914_ = lean_box(v_res_1913_);
return v_r_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1919_ = 0;
v___x_1920_ = l_Lean_Parser_quotedCharCoreFn(v___x_1918_, v___x_1919_, v_a_1916_, v_a_1917_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1924_ = 1;
v___x_1925_ = l_Lean_Parser_quotedCharCoreFn(v___x_1923_, v___x_1924_, v_a_1921_, v_a_1922_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1926_, lean_object* v_startPos_1927_, uint8_t v_includeWhitespace_1928_, lean_object* v_c_1929_, lean_object* v_s_1930_){
_start:
{
lean_object* v_pos_1931_; lean_object* v_errorMsg_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; uint8_t v___x_1935_; 
v_pos_1931_ = lean_ctor_get(v_s_1930_, 2);
v_errorMsg_1932_ = lean_ctor_get(v_s_1930_, 4);
v___x_1933_ = lean_box(0);
lean_inc(v_errorMsg_1932_);
v___x_1934_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1932_, v___x_1933_);
v___x_1935_ = lean_bool_not(v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v_toInputContext_1936_; lean_object* v_inputString_1937_; lean_object* v_endPos_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1960_; 
lean_inc(v_pos_1931_);
v_toInputContext_1936_ = lean_ctor_get(v_c_1929_, 0);
lean_inc_ref(v_toInputContext_1936_);
v_inputString_1937_ = lean_ctor_get(v_toInputContext_1936_, 0);
v_endPos_1938_ = lean_ctor_get(v_toInputContext_1936_, 3);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_toInputContext_1936_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; lean_object* v_unused_1962_; 
v_unused_1961_ = lean_ctor_get(v_toInputContext_1936_, 2);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_toInputContext_1936_, 1);
lean_dec(v_unused_1962_);
v___x_1940_ = v_toInputContext_1936_;
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_endPos_1938_);
lean_inc(v_inputString_1937_);
lean_dec(v_toInputContext_1936_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_leading_1942_; lean_object* v_val_1943_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1953_; lean_object* v_pos_1954_; 
lean_inc(v_startPos_1927_);
v_leading_1942_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1929_, v_startPos_1927_);
v_val_1943_ = lean_string_utf8_extract(v_inputString_1937_, v_startPos_1927_, v_pos_1931_);
if (v_includeWhitespace_1928_ == 0)
{
lean_dec_ref(v_c_1929_);
lean_inc(v_pos_1931_);
v___y_1953_ = v_s_1930_;
v_pos_1954_ = v_pos_1931_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_1958_; lean_object* v_pos_1959_; 
v___x_1958_ = l_Lean_Parser_whitespace(v_c_1929_, v_s_1930_);
v_pos_1959_ = lean_ctor_get(v___x_1958_, 2);
lean_inc(v_pos_1959_);
v___y_1953_ = v___x_1958_;
v_pos_1954_ = v_pos_1959_;
goto v___jp_1952_;
}
v___jp_1944_:
{
lean_object* v_info_1948_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 3, v_pos_1931_);
lean_ctor_set(v___x_1940_, 2, v___y_1946_);
lean_ctor_set(v___x_1940_, 1, v_startPos_1927_);
lean_ctor_set(v___x_1940_, 0, v_leading_1942_);
v_info_1948_ = v___x_1940_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_leading_1942_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_startPos_1927_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v___y_1946_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_pos_1931_);
v_info_1948_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = l_Lean_Syntax_mkLit(v_n_1926_, v_val_1943_, v_info_1948_);
v___x_1950_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1945_, v___x_1949_);
return v___x_1950_;
}
}
v___jp_1952_:
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_nat_dec_le(v_pos_1954_, v_endPos_1938_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_pos_1954_);
lean_inc(v_pos_1931_);
v___x_1956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1956_, 0, v_inputString_1937_);
lean_ctor_set(v___x_1956_, 1, v_pos_1931_);
lean_ctor_set(v___x_1956_, 2, v_endPos_1938_);
v___y_1945_ = v___y_1953_;
v___y_1946_ = v___x_1956_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1957_; 
lean_dec(v_endPos_1938_);
lean_inc(v_pos_1931_);
v___x_1957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1957_, 0, v_inputString_1937_);
lean_ctor_set(v___x_1957_, 1, v_pos_1931_);
lean_ctor_set(v___x_1957_, 2, v_pos_1954_);
v___y_1945_ = v___y_1953_;
v___y_1946_ = v___x_1957_;
goto v___jp_1944_;
}
}
}
}
else
{
lean_dec_ref(v_c_1929_);
lean_dec(v_startPos_1927_);
lean_dec(v_n_1926_);
return v_s_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1963_, lean_object* v_startPos_1964_, lean_object* v_includeWhitespace_1965_, lean_object* v_c_1966_, lean_object* v_s_1967_){
_start:
{
uint8_t v_includeWhitespace_boxed_1968_; lean_object* v_res_1969_; 
v_includeWhitespace_boxed_1968_ = lean_unbox(v_includeWhitespace_1965_);
v_res_1969_ = l_Lean_Parser_mkNodeToken(v_n_1963_, v_startPos_1964_, v_includeWhitespace_boxed_1968_, v_c_1966_, v_s_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1974_, lean_object* v_c_1975_, lean_object* v_s_1976_){
_start:
{
lean_object* v_pos_1977_; lean_object* v_toInputContext_1978_; uint8_t v___x_1979_; 
v_pos_1977_ = lean_ctor_get(v_s_1976_, 2);
v_toInputContext_1978_ = lean_ctor_get(v_c_1975_, 0);
v___x_1979_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1978_, v_pos_1977_);
if (v___x_1979_ == 0)
{
lean_object* v_inputString_1980_; uint8_t v___x_1981_; lean_object* v___y_1983_; uint32_t v_curr_1999_; lean_object* v___x_2000_; lean_object* v_s_2001_; uint32_t v___x_2002_; uint8_t v___x_2003_; 
v_inputString_1980_ = lean_ctor_get(v_toInputContext_1978_, 0);
v___x_1981_ = 1;
v_curr_1999_ = lean_string_utf8_get_fast(v_inputString_1980_, v_pos_1977_);
v___x_2000_ = lean_string_utf8_next_fast(v_inputString_1980_, v_pos_1977_);
v_s_2001_ = l_Lean_Parser_ParserState_setPos(v_s_1976_, v___x_2000_);
v___x_2002_ = 92;
v___x_2003_ = lean_uint32_dec_eq(v_curr_1999_, v___x_2002_);
if (v___x_2003_ == 0)
{
v___y_1983_ = v_s_2001_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2004_; 
lean_inc_ref(v_c_1975_);
v___x_2004_ = l_Lean_Parser_quotedCharFn(v_c_1975_, v_s_2001_);
v___y_1983_ = v___x_2004_;
goto v___jp_1982_;
}
v___jp_1982_:
{
lean_object* v_pos_1984_; lean_object* v_errorMsg_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; uint8_t v___x_1988_; 
v_pos_1984_ = lean_ctor_get(v___y_1983_, 2);
v_errorMsg_1985_ = lean_ctor_get(v___y_1983_, 4);
v___x_1986_ = lean_box(0);
lean_inc(v_errorMsg_1985_);
v___x_1987_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1985_, v___x_1986_);
v___x_1988_ = lean_bool_not(v___x_1987_);
if (v___x_1988_ == 0)
{
uint32_t v_curr_1989_; lean_object* v___x_1990_; lean_object* v_s_1991_; uint32_t v___x_1992_; uint8_t v___x_1993_; 
v_curr_1989_ = lean_string_utf8_get(v_inputString_1980_, v_pos_1984_);
v___x_1990_ = lean_string_utf8_next(v_inputString_1980_, v_pos_1984_);
v_s_1991_ = l_Lean_Parser_ParserState_setPos(v___y_1983_, v___x_1990_);
v___x_1992_ = 39;
v___x_1993_ = lean_uint32_dec_eq(v_curr_1989_, v___x_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec_ref(v_c_1975_);
lean_dec(v_startPos_1974_);
v___x_1994_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1995_ = lean_box(0);
v___x_1996_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1991_, v___x_1994_, v___x_1995_, v___x_1981_);
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1998_ = l_Lean_Parser_mkNodeToken(v___x_1997_, v_startPos_1974_, v___x_1981_, v_c_1975_, v_s_1991_);
return v___x_1998_;
}
}
else
{
lean_dec_ref(v_c_1975_);
lean_dec(v_startPos_1974_);
return v___y_1983_;
}
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref(v_c_1975_);
lean_dec(v_startPos_1974_);
v___x_2005_ = lean_box(0);
v___x_2006_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1976_, v___x_2005_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_2011_, lean_object* v_includeWhitespace_2012_, lean_object* v_c_2013_, lean_object* v_s_2014_){
_start:
{
uint8_t v_includeWhitespace_boxed_2015_; lean_object* v_res_2016_; 
v_includeWhitespace_boxed_2015_ = lean_unbox(v_includeWhitespace_2012_);
v_res_2016_ = l_Lean_Parser_strLitFnAux(v_startPos_2011_, v_includeWhitespace_boxed_2015_, v_c_2013_, v_s_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_2017_, uint8_t v_includeWhitespace_2018_, lean_object* v_c_2019_, lean_object* v_s_2020_){
_start:
{
lean_object* v_pos_2021_; lean_object* v_toInputContext_2022_; uint8_t v___x_2023_; 
v_pos_2021_ = lean_ctor_get(v_s_2020_, 2);
v_toInputContext_2022_ = lean_ctor_get(v_c_2019_, 0);
v___x_2023_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2022_, v_pos_2021_);
if (v___x_2023_ == 0)
{
lean_object* v_inputString_2024_; uint32_t v_curr_2025_; lean_object* v___x_2026_; lean_object* v_s_2027_; uint32_t v___x_2028_; uint8_t v___x_2029_; 
v_inputString_2024_ = lean_ctor_get(v_toInputContext_2022_, 0);
v_curr_2025_ = lean_string_utf8_get_fast(v_inputString_2024_, v_pos_2021_);
v___x_2026_ = lean_string_utf8_next_fast(v_inputString_2024_, v_pos_2021_);
v_s_2027_ = l_Lean_Parser_ParserState_setPos(v_s_2020_, v___x_2026_);
v___x_2028_ = 34;
v___x_2029_ = lean_uint32_dec_eq(v_curr_2025_, v___x_2028_);
if (v___x_2029_ == 0)
{
uint32_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = 92;
v___x_2031_ = lean_uint32_dec_eq(v_curr_2025_, v___x_2030_);
if (v___x_2031_ == 0)
{
v_s_2020_ = v_s_2027_;
goto _start;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2033_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2034_ = lean_box(v___x_2031_);
v___x_2035_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2035_, 0, v_startPos_2017_);
lean_closure_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_Parser_andthenFn(v___x_2033_, v___x_2035_, v_c_2019_, v_s_2027_);
return v___x_2036_;
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2038_ = l_Lean_Parser_mkNodeToken(v___x_2037_, v_startPos_2017_, v_includeWhitespace_2018_, v_c_2019_, v_s_2027_);
return v___x_2038_;
}
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v_c_2019_);
v___x_2039_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2040_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2020_, v___x_2039_, v_startPos_2017_);
return v___x_2040_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2041_, lean_object* v_i_2042_){
_start:
{
lean_object* v_toInputContext_2043_; uint8_t v___x_2044_; 
v_toInputContext_2043_ = lean_ctor_get(v_c_2041_, 0);
v___x_2044_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2043_, v_i_2042_);
if (v___x_2044_ == 0)
{
lean_object* v_inputString_2045_; uint32_t v_curr_2046_; uint32_t v___x_2047_; uint8_t v___x_2048_; 
v_inputString_2045_ = lean_ctor_get(v_toInputContext_2043_, 0);
v_curr_2046_ = lean_string_utf8_get_fast(v_inputString_2045_, v_i_2042_);
v___x_2047_ = 35;
v___x_2048_ = lean_uint32_dec_eq(v_curr_2046_, v___x_2047_);
if (v___x_2048_ == 0)
{
uint32_t v___x_2049_; uint8_t v___x_2050_; 
lean_dec(v_i_2042_);
v___x_2049_ = 34;
v___x_2050_ = lean_uint32_dec_eq(v_curr_2046_, v___x_2049_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_string_utf8_next_fast(v_inputString_2045_, v_i_2042_);
lean_dec(v_i_2042_);
v_i_2042_ = v___x_2051_;
goto _start;
}
}
else
{
uint8_t v___x_2053_; 
lean_dec(v_i_2042_);
v___x_2053_ = 0;
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2054_, lean_object* v_i_2055_){
_start:
{
uint8_t v_res_2056_; lean_object* v_r_2057_; 
v_res_2056_ = l_Lean_Parser_isRawStrLitStart(v_c_2054_, v_i_2055_);
lean_dec_ref(v_c_2054_);
v_r_2057_ = lean_box(v_res_2056_);
return v_r_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2059_, lean_object* v_s_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2062_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2060_, v___x_2061_, v_startPos_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2063_, lean_object* v_num_2064_, lean_object* v_closingNum_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_pos_2068_; lean_object* v_toInputContext_2069_; uint8_t v___x_2070_; 
v_pos_2068_ = lean_ctor_get(v_a_2067_, 2);
v_toInputContext_2069_ = lean_ctor_get(v_a_2066_, 0);
v___x_2070_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2069_, v_pos_2068_);
if (v___x_2070_ == 0)
{
lean_object* v_inputString_2071_; uint32_t v_curr_2072_; lean_object* v___x_2073_; lean_object* v_s_2074_; uint32_t v___x_2075_; uint8_t v___x_2076_; 
v_inputString_2071_ = lean_ctor_get(v_toInputContext_2069_, 0);
v_curr_2072_ = lean_string_utf8_get_fast(v_inputString_2071_, v_pos_2068_);
v___x_2073_ = lean_string_utf8_next_fast(v_inputString_2071_, v_pos_2068_);
v_s_2074_ = l_Lean_Parser_ParserState_setPos(v_a_2067_, v___x_2073_);
v___x_2075_ = 35;
v___x_2076_ = lean_uint32_dec_eq(v_curr_2072_, v___x_2075_);
if (v___x_2076_ == 0)
{
uint32_t v___x_2077_; uint8_t v___x_2078_; 
lean_dec(v_closingNum_2065_);
v___x_2077_ = 34;
v___x_2078_ = lean_uint32_dec_eq(v_curr_2072_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2063_, v_num_2064_, v_a_2066_, v_s_2074_);
return v___x_2079_;
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v_closingNum_2065_ = v___x_2080_;
v_a_2067_ = v_s_2074_;
goto _start;
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_nat_add(v_closingNum_2065_, v___x_2082_);
lean_dec(v_closingNum_2065_);
v___x_2084_ = lean_nat_dec_eq(v___x_2083_, v_num_2064_);
if (v___x_2084_ == 0)
{
v_closingNum_2065_ = v___x_2083_;
v_a_2067_ = v_s_2074_;
goto _start;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v___x_2083_);
v___x_2086_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2087_ = l_Lean_Parser_mkNodeToken(v___x_2086_, v_startPos_2063_, v___x_2084_, v_a_2066_, v_s_2074_);
return v___x_2087_;
}
}
}
else
{
lean_object* v___x_2088_; 
lean_dec_ref(v_a_2066_);
lean_dec(v_closingNum_2065_);
v___x_2088_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2063_, v_a_2067_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2089_, lean_object* v_num_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_pos_2093_; lean_object* v_toInputContext_2094_; uint8_t v___x_2095_; 
v_pos_2093_ = lean_ctor_get(v_a_2092_, 2);
v_toInputContext_2094_ = lean_ctor_get(v_a_2091_, 0);
v___x_2095_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2094_, v_pos_2093_);
if (v___x_2095_ == 0)
{
lean_object* v_inputString_2096_; uint32_t v_curr_2097_; lean_object* v___x_2098_; lean_object* v_s_2099_; uint32_t v___x_2100_; uint8_t v___x_2101_; 
v_inputString_2096_ = lean_ctor_get(v_toInputContext_2094_, 0);
v_curr_2097_ = lean_string_utf8_get_fast(v_inputString_2096_, v_pos_2093_);
v___x_2098_ = lean_string_utf8_next_fast(v_inputString_2096_, v_pos_2093_);
v_s_2099_ = l_Lean_Parser_ParserState_setPos(v_a_2092_, v___x_2098_);
v___x_2100_ = 34;
v___x_2101_ = lean_uint32_dec_eq(v_curr_2097_, v___x_2100_);
if (v___x_2101_ == 0)
{
v_a_2092_ = v_s_2099_;
goto _start;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = lean_nat_dec_eq(v_num_2090_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
v___x_2105_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2089_, v_num_2090_, v___x_2103_, v_a_2091_, v_s_2099_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2107_ = l_Lean_Parser_mkNodeToken(v___x_2106_, v_startPos_2089_, v___x_2104_, v_a_2091_, v_s_2099_);
return v___x_2107_;
}
}
}
else
{
lean_object* v___x_2108_; 
lean_dec_ref(v_a_2091_);
v___x_2108_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2089_, v_a_2092_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2109_, lean_object* v_num_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2109_, v_num_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_num_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2114_, lean_object* v_num_2115_, lean_object* v_closingNum_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2114_, v_num_2115_, v_closingNum_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_num_2115_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2120_, lean_object* v_num_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_pos_2124_; lean_object* v_toInputContext_2125_; uint8_t v___x_2126_; 
v_pos_2124_ = lean_ctor_get(v_a_2123_, 2);
v_toInputContext_2125_ = lean_ctor_get(v_a_2122_, 0);
v___x_2126_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2125_, v_pos_2124_);
if (v___x_2126_ == 0)
{
lean_object* v_inputString_2127_; uint32_t v_curr_2128_; lean_object* v___x_2129_; lean_object* v_s_2130_; uint32_t v___x_2131_; uint8_t v___x_2132_; 
v_inputString_2127_ = lean_ctor_get(v_toInputContext_2125_, 0);
v_curr_2128_ = lean_string_utf8_get_fast(v_inputString_2127_, v_pos_2124_);
v___x_2129_ = lean_string_utf8_next_fast(v_inputString_2127_, v_pos_2124_);
v_s_2130_ = l_Lean_Parser_ParserState_setPos(v_a_2123_, v___x_2129_);
v___x_2131_ = 35;
v___x_2132_ = lean_uint32_dec_eq(v_curr_2128_, v___x_2131_);
if (v___x_2132_ == 0)
{
uint32_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = 34;
v___x_2134_ = lean_uint32_dec_eq(v_curr_2128_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref(v_a_2122_);
lean_dec(v_num_2121_);
v___x_2135_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2120_, v_s_2130_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2120_, v_num_2121_, v_a_2122_, v_s_2130_);
lean_dec(v_num_2121_);
return v___x_2136_;
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_add(v_num_2121_, v___x_2137_);
lean_dec(v_num_2121_);
v_num_2121_ = v___x_2138_;
v_a_2123_ = v_s_2130_;
goto _start;
}
}
else
{
lean_object* v___x_2140_; 
lean_dec_ref(v_a_2122_);
lean_dec(v_num_2121_);
v___x_2140_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2120_, v_a_2123_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2141_, v___x_2144_, v_a_2142_, v_a_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2147_, lean_object* v_expecting_2148_, uint8_t v_needDigit_2149_, lean_object* v_c_2150_, lean_object* v_s_2151_){
_start:
{
lean_object* v_pos_2152_; lean_object* v_toInputContext_2153_; uint8_t v___x_2154_; 
v_pos_2152_ = lean_ctor_get(v_s_2151_, 2);
v_toInputContext_2153_ = lean_ctor_get(v_c_2150_, 0);
v___x_2154_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2153_, v_pos_2152_);
if (v___x_2154_ == 0)
{
lean_object* v_inputString_2155_; uint8_t v___x_2156_; uint32_t v_curr_2157_; uint32_t v___x_2158_; uint8_t v___x_2159_; 
v_inputString_2155_ = lean_ctor_get(v_toInputContext_2153_, 0);
v___x_2156_ = 1;
v_curr_2157_ = lean_string_utf8_get_fast(v_inputString_2155_, v_pos_2152_);
v___x_2158_ = 95;
v___x_2159_ = lean_uint32_dec_eq(v_curr_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2160_ = lean_box_uint32(v_curr_2157_);
lean_inc_ref(v_isDigit_2147_);
v___x_2161_ = lean_apply_1(v_isDigit_2147_, v___x_2160_);
v___x_2162_ = lean_unbox(v___x_2161_);
if (v___x_2162_ == 0)
{
lean_dec_ref(v_isDigit_2147_);
if (v_needDigit_2149_ == 0)
{
lean_dec_ref(v_expecting_2148_);
return v_s_2151_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_expecting_2148_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2151_, v___x_2163_, v___x_2165_, v___x_2156_);
return v___x_2166_;
}
}
else
{
lean_object* v___x_2167_; 
lean_inc(v_pos_2152_);
v___x_2167_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2151_, v_c_2150_, v_pos_2152_);
lean_dec(v_pos_2152_);
v_needDigit_2149_ = v___x_2159_;
v_s_2151_ = v___x_2167_;
goto _start;
}
}
else
{
lean_object* v___x_2169_; 
lean_inc(v_pos_2152_);
v___x_2169_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2151_, v_c_2150_, v_pos_2152_);
lean_dec(v_pos_2152_);
v_needDigit_2149_ = v___x_2156_;
v_s_2151_ = v___x_2169_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2147_);
if (v_needDigit_2149_ == 0)
{
lean_dec_ref(v_expecting_2148_);
return v_s_2151_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_expecting_2148_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2151_, v___x_2172_);
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2174_, lean_object* v_expecting_2175_, lean_object* v_needDigit_2176_, lean_object* v_c_2177_, lean_object* v_s_2178_){
_start:
{
uint8_t v_needDigit_boxed_2179_; lean_object* v_res_2180_; 
v_needDigit_boxed_2179_ = lean_unbox(v_needDigit_2176_);
v_res_2180_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2174_, v_expecting_2175_, v_needDigit_boxed_2179_, v_c_2177_, v_s_2178_);
lean_dec_ref(v_c_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2181_){
_start:
{
uint32_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = 48;
v___x_2183_ = lean_uint32_dec_le(v___x_2182_, v_c_2181_);
if (v___x_2183_ == 0)
{
return v___x_2183_;
}
else
{
uint32_t v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = 57;
v___x_2185_ = lean_uint32_dec_le(v_c_2181_, v___x_2184_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2186_){
_start:
{
uint32_t v_c_boxed_2187_; uint8_t v_res_2188_; lean_object* v_r_2189_; 
v_c_boxed_2187_ = lean_unbox_uint32(v_c_2186_);
lean_dec(v_c_2186_);
v_res_2188_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2187_);
v_r_2189_ = lean_box(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2194_, lean_object* v_c_2195_, lean_object* v_s_2196_, uint8_t v_hasBareDot_2197_){
_start:
{
lean_object* v_toInputContext_2198_; lean_object* v_pos_2199_; uint8_t v___x_2200_; 
v_toInputContext_2198_ = lean_ctor_get(v_c_2195_, 0);
v_pos_2199_ = lean_ctor_get(v_s_2196_, 2);
v___x_2200_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2198_, v_pos_2199_);
if (v___x_2200_ == 0)
{
lean_object* v_inputString_2201_; lean_object* v___f_2202_; uint8_t v___x_2203_; lean_object* v___y_2205_; uint8_t v___y_2206_; lean_object* v___y_2214_; lean_object* v___y_2221_; lean_object* v___y_2222_; uint32_t v_curr_2236_; uint8_t v___y_2238_; uint8_t v___y_2242_; uint32_t v___x_2251_; uint8_t v___x_2252_; 
v_inputString_2201_ = lean_ctor_get(v_toInputContext_2198_, 0);
v___f_2202_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2203_ = 1;
v_curr_2236_ = lean_string_utf8_get_fast(v_inputString_2201_, v_pos_2199_);
v___x_2251_ = 101;
v___x_2252_ = lean_uint32_dec_eq(v_curr_2236_, v___x_2251_);
if (v___x_2252_ == 0)
{
uint32_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = 69;
v___x_2254_ = lean_uint32_dec_eq(v_curr_2236_, v___x_2253_);
if (v___x_2254_ == 0)
{
if (v_hasBareDot_2197_ == 0)
{
lean_dec(v_startPos_2194_);
return v_s_2196_;
}
else
{
uint32_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = 65;
v___x_2256_ = lean_uint32_dec_le(v___x_2255_, v_curr_2236_);
if (v___x_2256_ == 0)
{
goto v___jp_2246_;
}
else
{
uint32_t v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = 90;
v___x_2258_ = lean_uint32_dec_le(v_curr_2236_, v___x_2257_);
if (v___x_2258_ == 0)
{
goto v___jp_2246_;
}
else
{
goto v___jp_2231_;
}
}
}
}
else
{
lean_dec(v_startPos_2194_);
goto v___jp_2224_;
}
}
else
{
lean_dec(v_startPos_2194_);
goto v___jp_2224_;
}
v___jp_2204_:
{
if (v___y_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v___y_2205_);
v___x_2207_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2208_ = lean_box(0);
v___x_2209_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2196_, v___x_2207_, v___x_2208_, v___x_2203_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2211_ = l_Lean_Parser_ParserState_setPos(v_s_2196_, v___y_2205_);
v___x_2212_ = l_Lean_Parser_takeDigitsFn(v___f_2202_, v___x_2210_, v___x_2200_, v_c_2195_, v___x_2211_);
return v___x_2212_;
}
}
v___jp_2213_:
{
uint32_t v_curr_2215_; uint32_t v___x_2216_; uint8_t v___x_2217_; 
v_curr_2215_ = lean_string_utf8_get(v_inputString_2201_, v___y_2214_);
v___x_2216_ = 48;
v___x_2217_ = lean_uint32_dec_le(v___x_2216_, v_curr_2215_);
if (v___x_2217_ == 0)
{
v___y_2205_ = v___y_2214_;
v___y_2206_ = v___x_2217_;
goto v___jp_2204_;
}
else
{
uint32_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = 57;
v___x_2219_ = lean_uint32_dec_le(v_curr_2215_, v___x_2218_);
v___y_2205_ = v___y_2214_;
v___y_2206_ = v___x_2219_;
goto v___jp_2204_;
}
}
v___jp_2220_:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_string_utf8_next(v___y_2222_, v___y_2221_);
lean_dec(v___y_2221_);
v___y_2214_ = v___x_2223_;
goto v___jp_2213_;
}
v___jp_2224_:
{
lean_object* v_i_2225_; uint32_t v___x_2226_; uint32_t v___x_2227_; uint8_t v___x_2228_; 
v_i_2225_ = lean_string_utf8_next(v_inputString_2201_, v_pos_2199_);
v___x_2226_ = lean_string_utf8_get(v_inputString_2201_, v_i_2225_);
v___x_2227_ = 45;
v___x_2228_ = lean_uint32_dec_eq(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
uint32_t v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = 43;
v___x_2230_ = lean_uint32_dec_eq(v___x_2226_, v___x_2229_);
if (v___x_2230_ == 0)
{
v___y_2214_ = v_i_2225_;
goto v___jp_2213_;
}
else
{
v___y_2221_ = v_i_2225_;
v___y_2222_ = v_inputString_2201_;
goto v___jp_2220_;
}
}
else
{
v___y_2221_ = v_i_2225_;
v___y_2222_ = v_inputString_2201_;
goto v___jp_2220_;
}
}
v___jp_2231_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = l_Lean_Parser_ParserState_setPos(v_s_2196_, v_startPos_2194_);
v___x_2233_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2234_ = lean_box(0);
v___x_2235_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2232_, v___x_2233_, v___x_2234_, v___x_2203_);
return v___x_2235_;
}
v___jp_2237_:
{
if (v___y_2238_ == 0)
{
uint32_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = 171;
v___x_2240_ = lean_uint32_dec_eq(v_curr_2236_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_dec(v_startPos_2194_);
return v_s_2196_;
}
else
{
goto v___jp_2231_;
}
}
else
{
goto v___jp_2231_;
}
}
v___jp_2241_:
{
if (v___y_2242_ == 0)
{
uint32_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = 95;
v___x_2244_ = lean_uint32_dec_eq(v_curr_2236_, v___x_2243_);
if (v___x_2244_ == 0)
{
uint8_t v___x_2245_; 
v___x_2245_ = l_Lean_isLetterLike(v_curr_2236_);
v___y_2238_ = v___x_2245_;
goto v___jp_2237_;
}
else
{
v___y_2238_ = v___x_2244_;
goto v___jp_2237_;
}
}
else
{
goto v___jp_2231_;
}
}
v___jp_2246_:
{
uint32_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = 97;
v___x_2248_ = lean_uint32_dec_le(v___x_2247_, v_curr_2236_);
if (v___x_2248_ == 0)
{
v___y_2242_ = v___x_2248_;
goto v___jp_2241_;
}
else
{
uint32_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = 122;
v___x_2250_ = lean_uint32_dec_le(v_curr_2236_, v___x_2249_);
v___y_2242_ = v___x_2250_;
goto v___jp_2241_;
}
}
}
else
{
lean_dec(v_startPos_2194_);
return v_s_2196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2259_, lean_object* v_c_2260_, lean_object* v_s_2261_, lean_object* v_hasBareDot_2262_){
_start:
{
uint8_t v_hasBareDot_boxed_2263_; lean_object* v_res_2264_; 
v_hasBareDot_boxed_2263_ = lean_unbox(v_hasBareDot_2262_);
v_res_2264_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2259_, v_c_2260_, v_s_2261_, v_hasBareDot_boxed_2263_);
lean_dec_ref(v_c_2260_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2265_, lean_object* v_s_2266_){
_start:
{
lean_object* v_toInputContext_2267_; lean_object* v_pos_2268_; lean_object* v_inputString_2269_; uint32_t v_curr_2270_; uint32_t v___x_2271_; uint8_t v___x_2272_; 
v_toInputContext_2267_ = lean_ctor_get(v_c_2265_, 0);
v_pos_2268_ = lean_ctor_get(v_s_2266_, 2);
v_inputString_2269_ = lean_ctor_get(v_toInputContext_2267_, 0);
v_curr_2270_ = lean_string_utf8_get(v_inputString_2269_, v_pos_2268_);
v___x_2271_ = 46;
v___x_2272_ = lean_uint32_dec_eq(v_curr_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v_s_2266_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
return v___x_2274_;
}
else
{
lean_object* v___f_2275_; lean_object* v_i_2276_; uint8_t v___y_2278_; uint32_t v_curr_2288_; uint32_t v___x_2289_; uint8_t v___x_2290_; 
v___f_2275_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_i_2276_ = lean_string_utf8_next(v_inputString_2269_, v_pos_2268_);
v_curr_2288_ = lean_string_utf8_get(v_inputString_2269_, v_i_2276_);
v___x_2289_ = 48;
v___x_2290_ = lean_uint32_dec_le(v___x_2289_, v_curr_2288_);
if (v___x_2290_ == 0)
{
v___y_2278_ = v___x_2290_;
goto v___jp_2277_;
}
else
{
uint32_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = 57;
v___x_2292_ = lean_uint32_dec_le(v_curr_2288_, v___x_2291_);
v___y_2278_ = v___x_2292_;
goto v___jp_2277_;
}
v___jp_2277_:
{
if (v___y_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = l_Lean_Parser_ParserState_setPos(v_s_2266_, v_i_2276_);
v___x_2280_ = lean_box(v___x_2272_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2283_ = 0;
v___x_2284_ = l_Lean_Parser_ParserState_setPos(v_s_2266_, v_i_2276_);
v___x_2285_ = l_Lean_Parser_takeDigitsFn(v___f_2275_, v___x_2282_, v___x_2283_, v_c_2265_, v___x_2284_);
v___x_2286_ = lean_box(v___x_2283_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2293_, lean_object* v_s_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2293_, v_s_2294_);
lean_dec_ref(v_c_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2299_, uint8_t v_includeWhitespace_2300_, lean_object* v_c_2301_, lean_object* v_s_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v_fst_2304_; lean_object* v_snd_2305_; uint8_t v___x_2306_; lean_object* v_s_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2303_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2301_, v_s_2302_);
v_fst_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_fst_2304_);
v_snd_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_snd_2305_);
lean_dec_ref(v___x_2303_);
v___x_2306_ = lean_unbox(v_snd_2305_);
lean_dec(v_snd_2305_);
lean_inc(v_startPos_2299_);
v_s_2307_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2299_, v_c_2301_, v_fst_2304_, v___x_2306_);
v___x_2308_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2309_ = l_Lean_Parser_mkNodeToken(v___x_2308_, v_startPos_2299_, v_includeWhitespace_2300_, v_c_2301_, v_s_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2310_, lean_object* v_includeWhitespace_2311_, lean_object* v_c_2312_, lean_object* v_s_2313_){
_start:
{
uint8_t v_includeWhitespace_boxed_2314_; lean_object* v_res_2315_; 
v_includeWhitespace_boxed_2314_ = lean_unbox(v_includeWhitespace_2311_);
v_res_2315_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2310_, v_includeWhitespace_boxed_2314_, v_c_2312_, v_s_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2319_, uint8_t v_includeWhitespace_2320_, lean_object* v_c_2321_, lean_object* v_s_2322_){
_start:
{
lean_object* v___f_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v_s_2326_; lean_object* v_pos_2327_; lean_object* v_toInputContext_2328_; uint8_t v___x_2329_; 
v___f_2323_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2324_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2325_ = 0;
v_s_2326_ = l_Lean_Parser_takeDigitsFn(v___f_2323_, v___x_2324_, v___x_2325_, v_c_2321_, v_s_2322_);
v_pos_2327_ = lean_ctor_get(v_s_2326_, 2);
lean_inc(v_pos_2327_);
v_toInputContext_2328_ = lean_ctor_get(v_c_2321_, 0);
v___x_2329_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2328_, v_pos_2327_);
if (v___x_2329_ == 0)
{
lean_object* v_inputString_2330_; uint32_t v_curr_2331_; uint8_t v___y_2345_; lean_object* v_j_2348_; uint8_t v___x_2354_; 
v_inputString_2330_ = lean_ctor_get(v_toInputContext_2328_, 0);
v_curr_2331_ = lean_string_utf8_get_fast(v_inputString_2330_, v_pos_2327_);
v_j_2348_ = lean_string_utf8_next(v_inputString_2330_, v_pos_2327_);
lean_dec(v_pos_2327_);
v___x_2354_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2328_, v_j_2348_);
if (v___x_2354_ == 0)
{
goto v___jp_2349_;
}
else
{
if (v___x_2329_ == 0)
{
lean_dec(v_j_2348_);
goto v___jp_2332_;
}
else
{
goto v___jp_2349_;
}
}
v___jp_2332_:
{
uint32_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = 46;
v___x_2334_ = lean_uint32_dec_eq(v_curr_2331_, v___x_2333_);
if (v___x_2334_ == 0)
{
uint32_t v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = 101;
v___x_2336_ = lean_uint32_dec_eq(v_curr_2331_, v___x_2335_);
if (v___x_2336_ == 0)
{
uint32_t v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = 69;
v___x_2338_ = lean_uint32_dec_eq(v_curr_2331_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2340_ = l_Lean_Parser_mkNodeToken(v___x_2339_, v_startPos_2319_, v_includeWhitespace_2320_, v_c_2321_, v_s_2326_);
return v___x_2340_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2319_, v_includeWhitespace_2320_, v_c_2321_, v_s_2326_);
return v___x_2341_;
}
}
else
{
lean_object* v___x_2342_; 
v___x_2342_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2319_, v_includeWhitespace_2320_, v_c_2321_, v_s_2326_);
return v___x_2342_;
}
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2319_, v_includeWhitespace_2320_, v_c_2321_, v_s_2326_);
return v___x_2343_;
}
}
v___jp_2344_:
{
if (v___y_2345_ == 0)
{
goto v___jp_2332_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2347_ = l_Lean_Parser_mkNodeToken(v___x_2346_, v_startPos_2319_, v_includeWhitespace_2320_, v_c_2321_, v_s_2326_);
return v___x_2347_;
}
}
v___jp_2349_:
{
uint32_t v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = 46;
v___x_2351_ = lean_uint32_dec_eq(v_curr_2331_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_dec(v_j_2348_);
v___y_2345_ = v___x_2351_;
goto v___jp_2344_;
}
else
{
uint32_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = lean_string_utf8_get_fast(v_inputString_2330_, v_j_2348_);
lean_dec(v_j_2348_);
v___x_2353_ = lean_uint32_dec_eq(v___x_2352_, v___x_2350_);
v___y_2345_ = v___x_2353_;
goto v___jp_2344_;
}
}
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_pos_2327_);
v___x_2355_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2356_ = l_Lean_Parser_mkNodeToken(v___x_2355_, v_startPos_2319_, v___x_2329_, v_c_2321_, v_s_2326_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2357_, lean_object* v_includeWhitespace_2358_, lean_object* v_c_2359_, lean_object* v_s_2360_){
_start:
{
uint8_t v_includeWhitespace_boxed_2361_; lean_object* v_res_2362_; 
v_includeWhitespace_boxed_2361_ = lean_unbox(v_includeWhitespace_2358_);
v_res_2362_ = l_Lean_Parser_decimalNumberFn(v_startPos_2357_, v_includeWhitespace_boxed_2361_, v_c_2359_, v_s_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2363_){
_start:
{
uint32_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = 48;
v___x_2365_ = lean_uint32_dec_eq(v_c_2363_, v___x_2364_);
if (v___x_2365_ == 0)
{
uint32_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = 49;
v___x_2367_ = lean_uint32_dec_eq(v_c_2363_, v___x_2366_);
return v___x_2367_;
}
else
{
return v___x_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2368_){
_start:
{
uint32_t v_c_boxed_2369_; uint8_t v_res_2370_; lean_object* v_r_2371_; 
v_c_boxed_2369_ = lean_unbox_uint32(v_c_2368_);
lean_dec(v_c_2368_);
v_res_2370_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2369_);
v_r_2371_ = lean_box(v_res_2370_);
return v_r_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2374_, uint8_t v_includeWhitespace_2375_, lean_object* v_c_2376_, lean_object* v_s_2377_){
_start:
{
lean_object* v___f_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v_s_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___f_2378_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2379_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2380_ = 1;
v_s_2381_ = l_Lean_Parser_takeDigitsFn(v___f_2378_, v___x_2379_, v___x_2380_, v_c_2376_, v_s_2377_);
v___x_2382_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2383_ = l_Lean_Parser_mkNodeToken(v___x_2382_, v_startPos_2374_, v_includeWhitespace_2375_, v_c_2376_, v_s_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2384_, lean_object* v_includeWhitespace_2385_, lean_object* v_c_2386_, lean_object* v_s_2387_){
_start:
{
uint8_t v_includeWhitespace_boxed_2388_; lean_object* v_res_2389_; 
v_includeWhitespace_boxed_2388_ = lean_unbox(v_includeWhitespace_2385_);
v_res_2389_ = l_Lean_Parser_binNumberFn(v_startPos_2384_, v_includeWhitespace_boxed_2388_, v_c_2386_, v_s_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2390_){
_start:
{
uint32_t v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = 48;
v___x_2392_ = lean_uint32_dec_le(v___x_2391_, v_c_2390_);
if (v___x_2392_ == 0)
{
return v___x_2392_;
}
else
{
uint32_t v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = 55;
v___x_2394_ = lean_uint32_dec_le(v_c_2390_, v___x_2393_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2395_){
_start:
{
uint32_t v_c_boxed_2396_; uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_c_boxed_2396_ = lean_unbox_uint32(v_c_2395_);
lean_dec(v_c_2395_);
v_res_2397_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2396_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2401_, uint8_t v_includeWhitespace_2402_, lean_object* v_c_2403_, lean_object* v_s_2404_){
_start:
{
lean_object* v___f_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v_s_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___f_2405_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2406_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2407_ = 1;
v_s_2408_ = l_Lean_Parser_takeDigitsFn(v___f_2405_, v___x_2406_, v___x_2407_, v_c_2403_, v_s_2404_);
v___x_2409_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2410_ = l_Lean_Parser_mkNodeToken(v___x_2409_, v_startPos_2401_, v_includeWhitespace_2402_, v_c_2403_, v_s_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2411_, lean_object* v_includeWhitespace_2412_, lean_object* v_c_2413_, lean_object* v_s_2414_){
_start:
{
uint8_t v_includeWhitespace_boxed_2415_; lean_object* v_res_2416_; 
v_includeWhitespace_boxed_2415_ = lean_unbox(v_includeWhitespace_2412_);
v_res_2416_ = l_Lean_Parser_octalNumberFn(v_startPos_2411_, v_includeWhitespace_boxed_2415_, v_c_2413_, v_s_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2417_){
_start:
{
uint8_t v___y_2419_; uint8_t v___y_2425_; uint32_t v___x_2430_; uint8_t v___x_2431_; 
v___x_2430_ = 48;
v___x_2431_ = lean_uint32_dec_le(v___x_2430_, v_c_2417_);
if (v___x_2431_ == 0)
{
v___y_2425_ = v___x_2431_;
goto v___jp_2424_;
}
else
{
uint32_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = 57;
v___x_2433_ = lean_uint32_dec_le(v_c_2417_, v___x_2432_);
v___y_2425_ = v___x_2433_;
goto v___jp_2424_;
}
v___jp_2418_:
{
if (v___y_2419_ == 0)
{
uint32_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = 65;
v___x_2421_ = lean_uint32_dec_le(v___x_2420_, v_c_2417_);
if (v___x_2421_ == 0)
{
return v___x_2421_;
}
else
{
uint32_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = 70;
v___x_2423_ = lean_uint32_dec_le(v_c_2417_, v___x_2422_);
return v___x_2423_;
}
}
else
{
return v___y_2419_;
}
}
v___jp_2424_:
{
if (v___y_2425_ == 0)
{
uint32_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = 97;
v___x_2427_ = lean_uint32_dec_le(v___x_2426_, v_c_2417_);
if (v___x_2427_ == 0)
{
v___y_2419_ = v___x_2427_;
goto v___jp_2418_;
}
else
{
uint32_t v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = 102;
v___x_2429_ = lean_uint32_dec_le(v_c_2417_, v___x_2428_);
v___y_2419_ = v___x_2429_;
goto v___jp_2418_;
}
}
else
{
return v___y_2425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2434_){
_start:
{
uint32_t v_c_boxed_2435_; uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_c_boxed_2435_ = lean_unbox_uint32(v_c_2434_);
lean_dec(v_c_2434_);
v_res_2436_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2435_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2438_){
_start:
{
uint8_t v___y_2440_; uint8_t v___y_2446_; uint32_t v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = 48;
v___x_2452_ = lean_uint32_dec_le(v___x_2451_, v___y_2438_);
if (v___x_2452_ == 0)
{
v___y_2446_ = v___x_2452_;
goto v___jp_2445_;
}
else
{
uint32_t v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = 57;
v___x_2454_ = lean_uint32_dec_le(v___y_2438_, v___x_2453_);
v___y_2446_ = v___x_2454_;
goto v___jp_2445_;
}
v___jp_2439_:
{
if (v___y_2440_ == 0)
{
uint32_t v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = 65;
v___x_2442_ = lean_uint32_dec_le(v___x_2441_, v___y_2438_);
if (v___x_2442_ == 0)
{
return v___x_2442_;
}
else
{
uint32_t v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = 70;
v___x_2444_ = lean_uint32_dec_le(v___y_2438_, v___x_2443_);
return v___x_2444_;
}
}
else
{
return v___y_2440_;
}
}
v___jp_2445_:
{
if (v___y_2446_ == 0)
{
uint32_t v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = 97;
v___x_2448_ = lean_uint32_dec_le(v___x_2447_, v___y_2438_);
if (v___x_2448_ == 0)
{
v___y_2440_ = v___x_2448_;
goto v___jp_2439_;
}
else
{
uint32_t v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = 102;
v___x_2450_ = lean_uint32_dec_le(v___y_2438_, v___x_2449_);
v___y_2440_ = v___x_2450_;
goto v___jp_2439_;
}
}
else
{
return v___y_2446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2455_){
_start:
{
uint32_t v___y_54__boxed_2456_; uint8_t v_res_2457_; lean_object* v_r_2458_; 
v___y_54__boxed_2456_ = lean_unbox_uint32(v___y_2455_);
lean_dec(v___y_2455_);
v_res_2457_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_54__boxed_2456_);
v_r_2458_ = lean_box(v_res_2457_);
return v_r_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2461_, uint8_t v_includeWhitespace_2462_, lean_object* v_kind_2463_, lean_object* v_c_2464_, lean_object* v_s_2465_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v_s_2469_; lean_object* v___x_2470_; 
v___f_2466_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2467_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2468_ = 1;
v_s_2469_ = l_Lean_Parser_takeDigitsFn(v___f_2466_, v___x_2467_, v___x_2468_, v_c_2464_, v_s_2465_);
v___x_2470_ = l_Lean_Parser_mkNodeToken(v_kind_2463_, v_startPos_2461_, v_includeWhitespace_2462_, v_c_2464_, v_s_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2471_, lean_object* v_includeWhitespace_2472_, lean_object* v_kind_2473_, lean_object* v_c_2474_, lean_object* v_s_2475_){
_start:
{
uint8_t v_includeWhitespace_boxed_2476_; lean_object* v_res_2477_; 
v_includeWhitespace_boxed_2476_ = lean_unbox(v_includeWhitespace_2472_);
v_res_2477_ = l_Lean_Parser_hexNumberFn(v_startPos_2471_, v_includeWhitespace_boxed_2476_, v_kind_2473_, v_c_2474_, v_s_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2479_, lean_object* v_c_2480_, lean_object* v_s_2481_){
_start:
{
lean_object* v_pos_2482_; uint8_t v___y_2484_; lean_object* v_toInputContext_2489_; uint8_t v___x_2490_; 
v_pos_2482_ = lean_ctor_get(v_s_2481_, 2);
v_toInputContext_2489_ = lean_ctor_get(v_c_2480_, 0);
v___x_2490_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2489_, v_pos_2482_);
if (v___x_2490_ == 0)
{
lean_object* v_inputString_2491_; uint32_t v_curr_2492_; uint32_t v___x_2493_; uint8_t v___x_2494_; 
v_inputString_2491_ = lean_ctor_get(v_toInputContext_2489_, 0);
v_curr_2492_ = lean_string_utf8_get_fast(v_inputString_2491_, v_pos_2482_);
v___x_2493_ = 48;
v___x_2494_ = lean_uint32_dec_eq(v_curr_2492_, v___x_2493_);
if (v___x_2494_ == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_uint32_dec_le(v___x_2493_, v_curr_2492_);
if (v___x_2495_ == 0)
{
v___y_2484_ = v___x_2495_;
goto v___jp_2483_;
}
else
{
uint32_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = 57;
v___x_2497_ = lean_uint32_dec_le(v_curr_2492_, v___x_2496_);
v___y_2484_ = v___x_2497_;
goto v___jp_2483_;
}
}
else
{
lean_object* v_i_2498_; uint32_t v_curr_2509_; uint32_t v___x_2510_; uint8_t v___x_2511_; 
lean_inc(v_pos_2482_);
v_i_2498_ = lean_string_utf8_next_fast(v_inputString_2491_, v_pos_2482_);
v_curr_2509_ = lean_string_utf8_get(v_inputString_2491_, v_i_2498_);
v___x_2510_ = 98;
v___x_2511_ = lean_uint32_dec_eq(v_curr_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
uint32_t v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = 66;
v___x_2513_ = lean_uint32_dec_eq(v_curr_2509_, v___x_2512_);
if (v___x_2513_ == 0)
{
uint32_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = 111;
v___x_2515_ = lean_uint32_dec_eq(v_curr_2509_, v___x_2514_);
if (v___x_2515_ == 0)
{
uint32_t v___x_2516_; uint8_t v___x_2517_; 
v___x_2516_ = 79;
v___x_2517_ = lean_uint32_dec_eq(v_curr_2509_, v___x_2516_);
if (v___x_2517_ == 0)
{
uint32_t v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = 120;
v___x_2519_ = lean_uint32_dec_eq(v_curr_2509_, v___x_2518_);
if (v___x_2519_ == 0)
{
uint32_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = 88;
v___x_2521_ = lean_uint32_dec_eq(v_curr_2509_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = l_Lean_Parser_ParserState_setPos(v_s_2481_, v_i_2498_);
v___x_2523_ = l_Lean_Parser_decimalNumberFn(v_pos_2482_, v_includeWhitespace_2479_, v_c_2480_, v___x_2522_);
return v___x_2523_;
}
else
{
goto v___jp_2499_;
}
}
else
{
goto v___jp_2499_;
}
}
else
{
goto v___jp_2503_;
}
}
else
{
goto v___jp_2503_;
}
}
else
{
goto v___jp_2506_;
}
}
else
{
goto v___jp_2506_;
}
v___jp_2499_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2501_ = l_Lean_Parser_ParserState_next(v_s_2481_, v_c_2480_, v_i_2498_);
v___x_2502_ = l_Lean_Parser_hexNumberFn(v_pos_2482_, v_includeWhitespace_2479_, v___x_2500_, v_c_2480_, v___x_2501_);
return v___x_2502_;
}
v___jp_2503_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = l_Lean_Parser_ParserState_next(v_s_2481_, v_c_2480_, v_i_2498_);
v___x_2505_ = l_Lean_Parser_octalNumberFn(v_pos_2482_, v_includeWhitespace_2479_, v_c_2480_, v___x_2504_);
return v___x_2505_;
}
v___jp_2506_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = l_Lean_Parser_ParserState_next(v_s_2481_, v_c_2480_, v_i_2498_);
v___x_2508_ = l_Lean_Parser_binNumberFn(v_pos_2482_, v_includeWhitespace_2479_, v_c_2480_, v___x_2507_);
return v___x_2508_;
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec_ref(v_c_2480_);
v___x_2524_ = lean_box(0);
v___x_2525_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2481_, v___x_2524_);
return v___x_2525_;
}
v___jp_2483_:
{
if (v___y_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v_c_2480_);
v___x_2485_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2486_ = l_Lean_Parser_ParserState_mkError(v_s_2481_, v___x_2485_);
return v___x_2486_;
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_inc(v_pos_2482_);
v___x_2487_ = l_Lean_Parser_ParserState_next(v_s_2481_, v_c_2480_, v_pos_2482_);
v___x_2488_ = l_Lean_Parser_decimalNumberFn(v_pos_2482_, v_includeWhitespace_2479_, v_c_2480_, v___x_2487_);
return v___x_2488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2526_, lean_object* v_c_2527_, lean_object* v_s_2528_){
_start:
{
uint8_t v_includeWhitespace_boxed_2529_; lean_object* v_res_2530_; 
v_includeWhitespace_boxed_2529_ = lean_unbox(v_includeWhitespace_2526_);
v_res_2530_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2529_, v_c_2527_, v_s_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2531_, lean_object* v_s_2532_){
_start:
{
lean_object* v_toInputContext_2533_; lean_object* v_pos_2534_; lean_object* v_inputString_2535_; uint32_t v_curr_2536_; uint32_t v___x_2537_; uint8_t v___x_2538_; 
v_toInputContext_2533_ = lean_ctor_get(v_c_2531_, 0);
v_pos_2534_ = lean_ctor_get(v_s_2532_, 2);
v_inputString_2535_ = lean_ctor_get(v_toInputContext_2533_, 0);
v_curr_2536_ = lean_string_utf8_get(v_inputString_2535_, v_pos_2534_);
v___x_2537_ = 46;
v___x_2538_ = lean_uint32_dec_eq(v_curr_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
return v___x_2538_;
}
else
{
lean_object* v_i_2539_; uint8_t v___x_2540_; 
v_i_2539_ = lean_string_utf8_next(v_inputString_2535_, v_pos_2534_);
v___x_2540_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2533_, v_i_2539_);
if (v___x_2540_ == 0)
{
uint32_t v_curr_2541_; uint8_t v___y_2543_; uint8_t v___y_2547_; uint32_t v___x_2556_; uint8_t v___x_2557_; 
v_curr_2541_ = lean_string_utf8_get(v_inputString_2535_, v_i_2539_);
lean_dec(v_i_2539_);
v___x_2556_ = 65;
v___x_2557_ = lean_uint32_dec_le(v___x_2556_, v_curr_2541_);
if (v___x_2557_ == 0)
{
goto v___jp_2551_;
}
else
{
uint32_t v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = 90;
v___x_2559_ = lean_uint32_dec_le(v_curr_2541_, v___x_2558_);
if (v___x_2559_ == 0)
{
goto v___jp_2551_;
}
else
{
return v___x_2538_;
}
}
v___jp_2542_:
{
if (v___y_2543_ == 0)
{
uint32_t v___x_2544_; uint8_t v___x_2545_; 
v___x_2544_ = 171;
v___x_2545_ = lean_uint32_dec_eq(v_curr_2541_, v___x_2544_);
return v___x_2545_;
}
else
{
return v___x_2538_;
}
}
v___jp_2546_:
{
if (v___y_2547_ == 0)
{
uint32_t v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = 95;
v___x_2549_ = lean_uint32_dec_eq(v_curr_2541_, v___x_2548_);
if (v___x_2549_ == 0)
{
uint8_t v___x_2550_; 
v___x_2550_ = l_Lean_isLetterLike(v_curr_2541_);
v___y_2543_ = v___x_2550_;
goto v___jp_2542_;
}
else
{
v___y_2543_ = v___x_2549_;
goto v___jp_2542_;
}
}
else
{
return v___x_2538_;
}
}
v___jp_2551_:
{
uint32_t v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = 97;
v___x_2553_ = lean_uint32_dec_le(v___x_2552_, v_curr_2541_);
if (v___x_2553_ == 0)
{
v___y_2547_ = v___x_2553_;
goto v___jp_2546_;
}
else
{
uint32_t v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = 122;
v___x_2555_ = lean_uint32_dec_le(v_curr_2541_, v___x_2554_);
v___y_2547_ = v___x_2555_;
goto v___jp_2546_;
}
}
}
else
{
uint8_t v___x_2560_; 
lean_dec(v_i_2539_);
v___x_2560_ = 0;
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2561_, lean_object* v_s_2562_){
_start:
{
uint8_t v_res_2563_; lean_object* v_r_2564_; 
v_res_2563_ = l_Lean_Parser_isIdCont(v_c_2561_, v_s_2562_);
lean_dec_ref(v_s_2562_);
lean_dec_ref(v_c_2561_);
v_r_2564_ = lean_box(v_res_2563_);
return v_r_2564_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2565_, lean_object* v_idStopPos_2566_, lean_object* v_tk_2567_){
_start:
{
if (lean_obj_tag(v_tk_2567_) == 0)
{
uint8_t v___x_2568_; 
v___x_2568_ = 0;
return v___x_2568_;
}
else
{
lean_object* v_val_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_val_2569_ = lean_ctor_get(v_tk_2567_, 0);
v___x_2570_ = lean_nat_sub(v_idStopPos_2566_, v_idStartPos_2565_);
v___x_2571_ = lean_string_utf8_byte_size(v_val_2569_);
v___x_2572_ = lean_nat_dec_le(v___x_2570_, v___x_2571_);
lean_dec(v___x_2570_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2573_, lean_object* v_idStopPos_2574_, lean_object* v_tk_2575_){
_start:
{
uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_res_2576_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2573_, v_idStopPos_2574_, v_tk_2575_);
lean_dec(v_tk_2575_);
lean_dec(v_idStopPos_2574_);
lean_dec(v_idStartPos_2573_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
if (lean_obj_tag(v_x_2578_) == 0)
{
if (lean_obj_tag(v_x_2579_) == 0)
{
uint8_t v___x_2580_; 
v___x_2580_ = 1;
return v___x_2580_;
}
else
{
uint8_t v___x_2581_; 
v___x_2581_ = 0;
return v___x_2581_;
}
}
else
{
if (lean_obj_tag(v_x_2579_) == 0)
{
uint8_t v___x_2582_; 
v___x_2582_ = 0;
return v___x_2582_;
}
else
{
lean_object* v_val_2583_; lean_object* v_val_2584_; uint8_t v___x_2585_; 
v_val_2583_ = lean_ctor_get(v_x_2578_, 0);
v_val_2584_ = lean_ctor_get(v_x_2579_, 0);
v___x_2585_ = lean_string_dec_eq(v_val_2583_, v_val_2584_);
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_x_2586_, lean_object* v_x_2587_){
_start:
{
uint8_t v_res_2588_; lean_object* v_r_2589_; 
v_res_2588_ = l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_x_2586_, v_x_2587_);
lean_dec(v_x_2587_);
lean_dec(v_x_2586_);
v_r_2589_ = lean_box(v_res_2588_);
return v_r_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2592_, lean_object* v_tk_2593_, lean_object* v_c_2594_, lean_object* v_s_2595_){
_start:
{
if (lean_obj_tag(v_tk_2593_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec_ref(v_c_2594_);
v___x_2596_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2597_ = lean_box(0);
v___x_2598_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2595_, v___x_2596_, v_startPos_2592_, v___x_2597_);
return v___x_2598_;
}
else
{
lean_object* v_toCacheableParserContext_2599_; lean_object* v_val_2600_; lean_object* v_toInputContext_2601_; lean_object* v_forbiddenTk_x3f_2602_; uint8_t v___x_2603_; 
v_toCacheableParserContext_2599_ = lean_ctor_get(v_c_2594_, 2);
v_val_2600_ = lean_ctor_get(v_tk_2593_, 0);
v_toInputContext_2601_ = lean_ctor_get(v_c_2594_, 0);
lean_inc_ref(v_toInputContext_2601_);
v_forbiddenTk_x3f_2602_ = lean_ctor_get(v_toCacheableParserContext_2599_, 3);
v___x_2603_ = l_Option_instBEq_beq___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTk_x3f_2602_, v_tk_2593_);
if (v___x_2603_ == 0)
{
lean_object* v_leading_2604_; lean_object* v___x_2605_; lean_object* v_stopPos_2606_; lean_object* v_s_2607_; lean_object* v_s_2608_; lean_object* v___y_2610_; lean_object* v_pos_2614_; lean_object* v_inputString_2615_; lean_object* v_endPos_2616_; uint8_t v___x_2617_; 
lean_inc(v_startPos_2592_);
v_leading_2604_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2594_, v_startPos_2592_);
v___x_2605_ = lean_string_utf8_byte_size(v_val_2600_);
v_stopPos_2606_ = lean_nat_add(v_startPos_2592_, v___x_2605_);
lean_inc(v_stopPos_2606_);
v_s_2607_ = l_Lean_Parser_ParserState_setPos(v_s_2595_, v_stopPos_2606_);
v_s_2608_ = l_Lean_Parser_whitespace(v_c_2594_, v_s_2607_);
v_pos_2614_ = lean_ctor_get(v_s_2608_, 2);
lean_inc(v_pos_2614_);
v_inputString_2615_ = lean_ctor_get(v_toInputContext_2601_, 0);
lean_inc_ref(v_inputString_2615_);
v_endPos_2616_ = lean_ctor_get(v_toInputContext_2601_, 3);
lean_inc(v_endPos_2616_);
lean_dec_ref(v_toInputContext_2601_);
v___x_2617_ = lean_nat_dec_le(v_pos_2614_, v_endPos_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
lean_dec(v_pos_2614_);
lean_inc(v_stopPos_2606_);
v___x_2618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2618_, 0, v_inputString_2615_);
lean_ctor_set(v___x_2618_, 1, v_stopPos_2606_);
lean_ctor_set(v___x_2618_, 2, v_endPos_2616_);
v___y_2610_ = v___x_2618_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2619_; 
lean_dec(v_endPos_2616_);
lean_inc(v_stopPos_2606_);
v___x_2619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2619_, 0, v_inputString_2615_);
lean_ctor_set(v___x_2619_, 1, v_stopPos_2606_);
lean_ctor_set(v___x_2619_, 2, v_pos_2614_);
v___y_2610_ = v___x_2619_;
goto v___jp_2609_;
}
v___jp_2609_:
{
lean_object* v___x_2611_; lean_object* v_atom_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2611_, 0, v_leading_2604_);
lean_ctor_set(v___x_2611_, 1, v_startPos_2592_);
lean_ctor_set(v___x_2611_, 2, v___y_2610_);
lean_ctor_set(v___x_2611_, 3, v_stopPos_2606_);
lean_inc(v_val_2600_);
v_atom_2612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2612_, 0, v___x_2611_);
lean_ctor_set(v_atom_2612_, 1, v_val_2600_);
v___x_2613_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2608_, v_atom_2612_);
return v___x_2613_;
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec_ref(v_toInputContext_2601_);
lean_dec_ref(v_c_2594_);
v___x_2620_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2595_, v___x_2620_, v_startPos_2592_, v___x_2621_);
return v___x_2622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2623_, lean_object* v_tk_2624_, lean_object* v_c_2625_, lean_object* v_s_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2623_, v_tk_2624_, v_c_2625_, v_s_2626_);
lean_dec(v_tk_2624_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2628_, lean_object* v_tk_2629_, lean_object* v_val_2630_, uint8_t v_includeWhitespace_2631_, lean_object* v_c_2632_, lean_object* v_s_2633_){
_start:
{
lean_object* v_pos_2634_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___x_2644_; 
v_pos_2634_ = lean_ctor_get(v_s_2633_, 2);
v___x_2644_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2628_, v_pos_2634_, v_tk_2629_);
if (v___x_2644_ == 0)
{
lean_object* v_toInputContext_2645_; lean_object* v_inputString_2646_; lean_object* v_endPos_2647_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v_pos_2651_; lean_object* v___y_2657_; uint8_t v___x_2660_; 
lean_inc(v_pos_2634_);
v_toInputContext_2645_ = lean_ctor_get(v_c_2632_, 0);
v_inputString_2646_ = lean_ctor_get(v_toInputContext_2645_, 0);
lean_inc_ref(v_inputString_2646_);
v_endPos_2647_ = lean_ctor_get(v_toInputContext_2645_, 3);
lean_inc(v_endPos_2647_);
v___x_2660_ = lean_nat_dec_le(v_pos_2634_, v_endPos_2647_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; 
lean_inc(v_endPos_2647_);
lean_inc(v_startPos_2628_);
lean_inc_ref(v_inputString_2646_);
v___x_2661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2661_, 0, v_inputString_2646_);
lean_ctor_set(v___x_2661_, 1, v_startPos_2628_);
lean_ctor_set(v___x_2661_, 2, v_endPos_2647_);
v___y_2657_ = v___x_2661_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2662_; 
lean_inc(v_pos_2634_);
lean_inc(v_startPos_2628_);
lean_inc_ref(v_inputString_2646_);
v___x_2662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2662_, 0, v_inputString_2646_);
lean_ctor_set(v___x_2662_, 1, v_startPos_2628_);
lean_ctor_set(v___x_2662_, 2, v_pos_2634_);
v___y_2657_ = v___x_2662_;
goto v___jp_2656_;
}
v___jp_2648_:
{
lean_object* v_leading_2652_; uint8_t v___x_2653_; 
lean_inc(v_startPos_2628_);
v_leading_2652_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2632_, v_startPos_2628_);
lean_dec_ref(v_c_2632_);
v___x_2653_ = lean_nat_dec_le(v_pos_2651_, v_endPos_2647_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec(v_pos_2651_);
lean_inc(v_pos_2634_);
v___x_2654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2654_, 0, v_inputString_2646_);
lean_ctor_set(v___x_2654_, 1, v_pos_2634_);
lean_ctor_set(v___x_2654_, 2, v_endPos_2647_);
v___y_2636_ = v___y_2650_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v_leading_2652_;
v___y_2639_ = v___x_2654_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2655_; 
lean_dec(v_endPos_2647_);
lean_inc(v_pos_2634_);
v___x_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2655_, 0, v_inputString_2646_);
lean_ctor_set(v___x_2655_, 1, v_pos_2634_);
lean_ctor_set(v___x_2655_, 2, v_pos_2651_);
v___y_2636_ = v___y_2650_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v_leading_2652_;
v___y_2639_ = v___x_2655_;
goto v___jp_2635_;
}
}
v___jp_2656_:
{
if (v_includeWhitespace_2631_ == 0)
{
lean_inc(v_pos_2634_);
v___y_2649_ = v___y_2657_;
v___y_2650_ = v_s_2633_;
v_pos_2651_ = v_pos_2634_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2658_; lean_object* v_pos_2659_; 
lean_inc_ref(v_c_2632_);
v___x_2658_ = l_Lean_Parser_whitespace(v_c_2632_, v_s_2633_);
v_pos_2659_ = lean_ctor_get(v___x_2658_, 2);
lean_inc(v_pos_2659_);
v___y_2649_ = v___y_2657_;
v___y_2650_ = v___x_2658_;
v_pos_2651_ = v_pos_2659_;
goto v___jp_2648_;
}
}
}
else
{
lean_object* v___x_2663_; 
lean_dec(v_val_2630_);
v___x_2663_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2628_, v_tk_2629_, v_c_2632_, v_s_2633_);
return v___x_2663_;
}
v___jp_2635_:
{
lean_object* v_info_2640_; lean_object* v___x_2641_; lean_object* v_atom_2642_; lean_object* v___x_2643_; 
v_info_2640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2640_, 0, v___y_2638_);
lean_ctor_set(v_info_2640_, 1, v_startPos_2628_);
lean_ctor_set(v_info_2640_, 2, v___y_2639_);
lean_ctor_set(v_info_2640_, 3, v_pos_2634_);
v___x_2641_ = lean_box(0);
v_atom_2642_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2642_, 0, v_info_2640_);
lean_ctor_set(v_atom_2642_, 1, v___y_2637_);
lean_ctor_set(v_atom_2642_, 2, v_val_2630_);
lean_ctor_set(v_atom_2642_, 3, v___x_2641_);
v___x_2643_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2636_, v_atom_2642_);
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2664_, lean_object* v_tk_2665_, lean_object* v_val_2666_, lean_object* v_includeWhitespace_2667_, lean_object* v_c_2668_, lean_object* v_s_2669_){
_start:
{
uint8_t v_includeWhitespace_boxed_2670_; lean_object* v_res_2671_; 
v_includeWhitespace_boxed_2670_ = lean_unbox(v_includeWhitespace_2667_);
v_res_2671_ = l_Lean_Parser_mkIdResult(v_startPos_2664_, v_tk_2665_, v_val_2666_, v_includeWhitespace_boxed_2670_, v_c_2668_, v_s_2669_);
lean_dec(v_tk_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2672_){
_start:
{
uint8_t v___y_2674_; uint8_t v___y_2686_; uint32_t v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = 65;
v___x_2697_ = lean_uint32_dec_le(v___x_2696_, v___y_2672_);
if (v___x_2697_ == 0)
{
goto v___jp_2691_;
}
else
{
uint32_t v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = 90;
v___x_2699_ = lean_uint32_dec_le(v___y_2672_, v___x_2698_);
if (v___x_2699_ == 0)
{
goto v___jp_2691_;
}
else
{
return v___x_2699_;
}
}
v___jp_2673_:
{
if (v___y_2674_ == 0)
{
uint32_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = 95;
v___x_2676_ = lean_uint32_dec_eq(v___y_2672_, v___x_2675_);
if (v___x_2676_ == 0)
{
uint32_t v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = 39;
v___x_2678_ = lean_uint32_dec_eq(v___y_2672_, v___x_2677_);
if (v___x_2678_ == 0)
{
uint32_t v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = 33;
v___x_2680_ = lean_uint32_dec_eq(v___y_2672_, v___x_2679_);
if (v___x_2680_ == 0)
{
uint32_t v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = 63;
v___x_2682_ = lean_uint32_dec_eq(v___y_2672_, v___x_2681_);
if (v___x_2682_ == 0)
{
uint8_t v___x_2683_; 
v___x_2683_ = l_Lean_isLetterLike(v___y_2672_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
v___x_2684_ = l_Lean_isSubScriptAlnum(v___y_2672_);
return v___x_2684_;
}
else
{
return v___x_2683_;
}
}
else
{
return v___x_2682_;
}
}
else
{
return v___x_2680_;
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
return v___y_2674_;
}
}
v___jp_2685_:
{
if (v___y_2686_ == 0)
{
uint32_t v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = 48;
v___x_2688_ = lean_uint32_dec_le(v___x_2687_, v___y_2672_);
if (v___x_2688_ == 0)
{
v___y_2674_ = v___x_2688_;
goto v___jp_2673_;
}
else
{
uint32_t v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = 57;
v___x_2690_ = lean_uint32_dec_le(v___y_2672_, v___x_2689_);
v___y_2674_ = v___x_2690_;
goto v___jp_2673_;
}
}
else
{
return v___y_2686_;
}
}
v___jp_2691_:
{
uint32_t v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = 97;
v___x_2693_ = lean_uint32_dec_le(v___x_2692_, v___y_2672_);
if (v___x_2693_ == 0)
{
v___y_2686_ = v___x_2693_;
goto v___jp_2685_;
}
else
{
uint32_t v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = 122;
v___x_2695_ = lean_uint32_dec_le(v___y_2672_, v___x_2694_);
v___y_2686_ = v___x_2695_;
goto v___jp_2685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2700_){
_start:
{
uint32_t v___y_633__boxed_2701_; uint8_t v_res_2702_; lean_object* v_r_2703_; 
v___y_633__boxed_2701_ = lean_unbox_uint32(v___y_2700_);
lean_dec(v___y_2700_);
v_res_2702_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_633__boxed_2701_);
v_r_2703_ = lean_box(v_res_2702_);
return v_r_2703_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2704_){
_start:
{
uint32_t v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = 187;
v___x_2706_ = lean_uint32_dec_eq(v___y_2704_, v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2707_){
_start:
{
uint32_t v___y_690__boxed_2708_; uint8_t v_res_2709_; lean_object* v_r_2710_; 
v___y_690__boxed_2708_ = lean_unbox_uint32(v___y_2707_);
lean_dec(v___y_2707_);
v_res_2709_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_690__boxed_2708_);
v_r_2710_ = lean_box(v_res_2709_);
return v_r_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2714_, lean_object* v_tk_2715_, uint8_t v_includeWhitespace_2716_, lean_object* v_r_2717_, lean_object* v_c_2718_, lean_object* v_s_2719_){
_start:
{
lean_object* v_pos_2720_; lean_object* v_toInputContext_2721_; uint8_t v___x_2722_; 
v_pos_2720_ = lean_ctor_get(v_s_2719_, 2);
v_toInputContext_2721_ = lean_ctor_get(v_c_2718_, 0);
v___x_2722_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2721_, v_pos_2720_);
if (v___x_2722_ == 0)
{
lean_object* v_inputString_2723_; uint32_t v_curr_2724_; uint32_t v___x_2725_; uint8_t v___x_2726_; 
v_inputString_2723_ = lean_ctor_get(v_toInputContext_2721_, 0);
v_curr_2724_ = lean_string_utf8_get_fast(v_inputString_2723_, v_pos_2720_);
v___x_2725_ = 171;
v___x_2726_ = lean_uint32_dec_eq(v_curr_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___f_2727_; uint8_t v___y_2739_; uint8_t v___y_2742_; uint32_t v___x_2751_; uint8_t v___x_2752_; 
v___f_2727_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2751_ = 65;
v___x_2752_ = lean_uint32_dec_le(v___x_2751_, v_curr_2724_);
if (v___x_2752_ == 0)
{
goto v___jp_2746_;
}
else
{
uint32_t v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = 90;
v___x_2754_ = lean_uint32_dec_le(v_curr_2724_, v___x_2753_);
if (v___x_2754_ == 0)
{
goto v___jp_2746_;
}
else
{
lean_inc(v_pos_2720_);
goto v___jp_2728_;
}
}
v___jp_2728_:
{
lean_object* v___x_2729_; lean_object* v_s_2730_; lean_object* v_pos_2731_; lean_object* v___x_2732_; lean_object* v_r_2733_; uint8_t v___x_2734_; 
v___x_2729_ = l_Lean_Parser_ParserState_next(v_s_2719_, v_c_2718_, v_pos_2720_);
v_s_2730_ = l_Lean_Parser_takeWhileFn(v___f_2727_, v_c_2718_, v___x_2729_);
v_pos_2731_ = lean_ctor_get(v_s_2730_, 2);
lean_inc(v_pos_2731_);
v___x_2732_ = lean_string_utf8_extract(v_inputString_2723_, v_pos_2720_, v_pos_2731_);
lean_dec(v_pos_2720_);
v_r_2733_ = l_Lean_Name_str___override(v_r_2717_, v___x_2732_);
v___x_2734_ = l_Lean_Parser_isIdCont(v_c_2718_, v_s_2730_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
lean_dec(v_pos_2731_);
v___x_2735_ = l_Lean_Parser_mkIdResult(v_startPos_2714_, v_tk_2715_, v_r_2733_, v_includeWhitespace_2716_, v_c_2718_, v_s_2730_);
return v___x_2735_;
}
else
{
lean_object* v_s_2736_; 
v_s_2736_ = l_Lean_Parser_ParserState_next(v_s_2730_, v_c_2718_, v_pos_2731_);
lean_dec(v_pos_2731_);
v_r_2717_ = v_r_2733_;
v_s_2719_ = v_s_2736_;
goto _start;
}
}
v___jp_2738_:
{
if (v___y_2739_ == 0)
{
lean_object* v___x_2740_; 
lean_dec(v_r_2717_);
v___x_2740_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2714_, v_tk_2715_, v_c_2718_, v_s_2719_);
return v___x_2740_;
}
else
{
lean_inc(v_pos_2720_);
goto v___jp_2728_;
}
}
v___jp_2741_:
{
if (v___y_2742_ == 0)
{
uint32_t v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = 95;
v___x_2744_ = lean_uint32_dec_eq(v_curr_2724_, v___x_2743_);
if (v___x_2744_ == 0)
{
uint8_t v___x_2745_; 
v___x_2745_ = l_Lean_isLetterLike(v_curr_2724_);
v___y_2739_ = v___x_2745_;
goto v___jp_2738_;
}
else
{
v___y_2739_ = v___x_2744_;
goto v___jp_2738_;
}
}
else
{
lean_inc(v_pos_2720_);
goto v___jp_2728_;
}
}
v___jp_2746_:
{
uint32_t v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = 97;
v___x_2748_ = lean_uint32_dec_le(v___x_2747_, v_curr_2724_);
if (v___x_2748_ == 0)
{
v___y_2742_ = v___x_2748_;
goto v___jp_2741_;
}
else
{
uint32_t v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = 122;
v___x_2750_ = lean_uint32_dec_le(v_curr_2724_, v___x_2749_);
v___y_2742_ = v___x_2750_;
goto v___jp_2741_;
}
}
}
else
{
lean_object* v___f_2755_; lean_object* v_startPart_2756_; lean_object* v___x_2757_; lean_object* v_s_2758_; lean_object* v_pos_2759_; uint8_t v___x_2760_; 
v___f_2755_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2756_ = lean_string_utf8_next_fast(v_inputString_2723_, v_pos_2720_);
v___x_2757_ = l_Lean_Parser_ParserState_setPos(v_s_2719_, v_startPart_2756_);
v_s_2758_ = l_Lean_Parser_takeUntilFn(v___f_2755_, v_c_2718_, v___x_2757_);
v_pos_2759_ = lean_ctor_get(v_s_2758_, 2);
lean_inc(v_pos_2759_);
v___x_2760_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2721_, v_pos_2759_);
if (v___x_2760_ == 0)
{
lean_object* v_s_2761_; lean_object* v___x_2762_; lean_object* v_r_2763_; uint8_t v___x_2764_; 
v_s_2761_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2758_, v_c_2718_, v_pos_2759_);
v___x_2762_ = lean_string_utf8_extract(v_inputString_2723_, v_startPart_2756_, v_pos_2759_);
lean_dec(v_pos_2759_);
v_r_2763_ = l_Lean_Name_str___override(v_r_2717_, v___x_2762_);
v___x_2764_ = l_Lean_Parser_isIdCont(v_c_2718_, v_s_2761_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Parser_mkIdResult(v_startPos_2714_, v_tk_2715_, v_r_2763_, v_includeWhitespace_2716_, v_c_2718_, v_s_2761_);
return v___x_2765_;
}
else
{
lean_object* v_pos_2766_; lean_object* v_s_2767_; 
v_pos_2766_ = lean_ctor_get(v_s_2761_, 2);
lean_inc(v_pos_2766_);
v_s_2767_ = l_Lean_Parser_ParserState_next(v_s_2761_, v_c_2718_, v_pos_2766_);
lean_dec(v_pos_2766_);
v_r_2717_ = v_r_2763_;
v_s_2719_ = v_s_2767_;
goto _start;
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec(v_pos_2759_);
lean_dec_ref(v_c_2718_);
lean_dec(v_r_2717_);
lean_dec(v_startPos_2714_);
v___x_2769_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2770_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2758_, v___x_2769_, v_startPart_2756_);
return v___x_2770_;
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec_ref(v_c_2718_);
lean_dec(v_r_2717_);
lean_dec(v_startPos_2714_);
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2719_, v___x_2771_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2773_, lean_object* v_tk_2774_, lean_object* v_includeWhitespace_2775_, lean_object* v_r_2776_, lean_object* v_c_2777_, lean_object* v_s_2778_){
_start:
{
uint8_t v_includeWhitespace_boxed_2779_; lean_object* v_res_2780_; 
v_includeWhitespace_boxed_2779_ = lean_unbox(v_includeWhitespace_2775_);
v_res_2780_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2773_, v_tk_2774_, v_includeWhitespace_boxed_2779_, v_r_2776_, v_c_2777_, v_s_2778_);
lean_dec(v_tk_2774_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2781_, lean_object* v_tk_2782_, lean_object* v_r_2783_, uint8_t v_includeWhitespace_2784_, lean_object* v_c_2785_, lean_object* v_s_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2781_, v_tk_2782_, v_includeWhitespace_2784_, v_r_2783_, v_c_2785_, v_s_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2788_, lean_object* v_tk_2789_, lean_object* v_r_2790_, lean_object* v_includeWhitespace_2791_, lean_object* v_c_2792_, lean_object* v_s_2793_){
_start:
{
uint8_t v_includeWhitespace_boxed_2794_; lean_object* v_res_2795_; 
v_includeWhitespace_boxed_2794_ = lean_unbox(v_includeWhitespace_2791_);
v_res_2795_ = l_Lean_Parser_identFnAux(v_startPos_2788_, v_tk_2789_, v_r_2790_, v_includeWhitespace_boxed_2794_, v_c_2792_, v_s_2793_);
lean_dec(v_tk_2789_);
return v_res_2795_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2796_){
_start:
{
uint8_t v___y_2798_; uint8_t v___y_2802_; uint32_t v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = 65;
v___x_2812_ = lean_uint32_dec_le(v___x_2811_, v_c_2796_);
if (v___x_2812_ == 0)
{
goto v___jp_2806_;
}
else
{
uint32_t v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = 90;
v___x_2814_ = lean_uint32_dec_le(v_c_2796_, v___x_2813_);
if (v___x_2814_ == 0)
{
goto v___jp_2806_;
}
else
{
return v___x_2814_;
}
}
v___jp_2797_:
{
if (v___y_2798_ == 0)
{
uint32_t v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = 171;
v___x_2800_ = lean_uint32_dec_eq(v_c_2796_, v___x_2799_);
return v___x_2800_;
}
else
{
return v___y_2798_;
}
}
v___jp_2801_:
{
if (v___y_2802_ == 0)
{
uint32_t v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = 95;
v___x_2804_ = lean_uint32_dec_eq(v_c_2796_, v___x_2803_);
if (v___x_2804_ == 0)
{
uint8_t v___x_2805_; 
v___x_2805_ = l_Lean_isLetterLike(v_c_2796_);
v___y_2798_ = v___x_2805_;
goto v___jp_2797_;
}
else
{
v___y_2798_ = v___x_2804_;
goto v___jp_2797_;
}
}
else
{
return v___y_2802_;
}
}
v___jp_2806_:
{
uint32_t v___x_2807_; uint8_t v___x_2808_; 
v___x_2807_ = 97;
v___x_2808_ = lean_uint32_dec_le(v___x_2807_, v_c_2796_);
if (v___x_2808_ == 0)
{
v___y_2802_ = v___x_2808_;
goto v___jp_2801_;
}
else
{
uint32_t v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = 122;
v___x_2810_ = lean_uint32_dec_le(v_c_2796_, v___x_2809_);
v___y_2802_ = v___x_2810_;
goto v___jp_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2815_){
_start:
{
uint32_t v_c_boxed_2816_; uint8_t v_res_2817_; lean_object* v_r_2818_; 
v_c_boxed_2816_ = lean_unbox_uint32(v_c_2815_);
lean_dec(v_c_2815_);
v_res_2817_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2816_);
v_r_2818_ = lean_box(v_res_2817_);
return v_r_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2820_, lean_object* v_c_2821_, lean_object* v_s_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v_s_2827_; lean_object* v_stxStack_2828_; lean_object* v_errorMsg_2829_; uint8_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_box(0);
v___x_2825_ = 1;
v___x_2826_ = l_Lean_Parser_ParserState_next(v_s_2822_, v_c_2821_, v_startPos_2820_);
v_s_2827_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2820_, v___x_2823_, v___x_2825_, v___x_2824_, v_c_2821_, v___x_2826_);
v_stxStack_2828_ = lean_ctor_get(v_s_2827_, 0);
lean_inc_ref(v_stxStack_2828_);
v_errorMsg_2829_ = lean_ctor_get(v_s_2827_, 4);
lean_inc(v_errorMsg_2829_);
v___x_2830_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2829_, v___x_2823_);
v___x_2831_ = lean_bool_not(v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v_stx_2832_; 
v_stx_2832_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2828_);
lean_dec_ref(v_stxStack_2828_);
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
v_s_2838_ = l_Lean_Parser_ParserState_popSyntax(v_s_2827_);
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
v___x_2843_ = l_Lean_Parser_ParserState_mkError(v_s_2827_, v___x_2842_);
return v___x_2843_;
}
}
else
{
lean_dec_ref(v_stxStack_2828_);
return v_s_2827_;
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
lean_object* v___x_2887_; uint32_t v___x_2888_; uint8_t v___x_2889_; uint8_t v___x_2890_; 
v___x_2887_ = lean_string_utf8_next(v_inputString_2849_, v_pos_2847_);
v___x_2888_ = lean_string_utf8_get(v_inputString_2849_, v___x_2887_);
lean_dec(v___x_2887_);
v___x_2889_ = lean_uint32_dec_eq(v___x_2888_, v___x_2885_);
v___x_2890_ = lean_bool_not(v___x_2889_);
v___y_2878_ = v___x_2890_;
goto v___jp_2877_;
}
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_inc(v_pos_2847_);
v___x_2891_ = l_Lean_Parser_ParserState_next(v_s_2845_, v_c_2844_, v_pos_2847_);
v___x_2892_ = l_Lean_Parser_strLitFnAux(v_pos_2847_, v___x_2854_, v_c_2844_, v___x_2891_);
return v___x_2892_;
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2893_, lean_object* v_s_2894_){
_start:
{
lean_object* v_cache_2895_; lean_object* v_errorMsg_2896_; 
v_cache_2895_ = lean_ctor_get(v_s_2894_, 3);
lean_inc_ref(v_cache_2895_);
v_errorMsg_2896_ = lean_ctor_get(v_s_2894_, 4);
if (lean_obj_tag(v_errorMsg_2896_) == 0)
{
lean_object* v_stxStack_2897_; lean_object* v_lhsPrec_2898_; lean_object* v_pos_2899_; lean_object* v_recoveredErrors_2900_; lean_object* v_parserCache_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2926_; 
v_stxStack_2897_ = lean_ctor_get(v_s_2894_, 0);
v_lhsPrec_2898_ = lean_ctor_get(v_s_2894_, 1);
v_pos_2899_ = lean_ctor_get(v_s_2894_, 2);
v_recoveredErrors_2900_ = lean_ctor_get(v_s_2894_, 5);
v_parserCache_2901_ = lean_ctor_get(v_cache_2895_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_cache_2895_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v_cache_2895_, 0);
lean_dec(v_unused_2927_);
v___x_2903_ = v_cache_2895_;
v_isShared_2904_ = v_isSharedCheck_2926_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_parserCache_2901_);
lean_dec(v_cache_2895_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2926_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2897_);
v___x_2906_ = lean_unsigned_to_nat(0u);
v___x_2907_ = lean_nat_dec_eq(v___x_2905_, v___x_2906_);
lean_dec(v___x_2905_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2919_; 
lean_inc_ref(v_recoveredErrors_2900_);
lean_inc(v_pos_2899_);
lean_inc(v_lhsPrec_2898_);
lean_inc_ref(v_stxStack_2897_);
lean_inc(v_errorMsg_2896_);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_s_2894_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2920_ = lean_ctor_get(v_s_2894_, 5);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_s_2894_, 4);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_s_2894_, 3);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_s_2894_, 2);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_s_2894_, 1);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_s_2894_, 0);
lean_dec(v_unused_2925_);
v___x_2909_ = v_s_2894_;
v_isShared_2910_ = v_isSharedCheck_2919_;
goto v_resetjp_2908_;
}
else
{
lean_dec(v_s_2894_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2919_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_tk_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v_tk_2911_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2897_);
lean_inc(v_pos_2899_);
v___x_2912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2912_, 0, v_startPos_2893_);
lean_ctor_set(v___x_2912_, 1, v_pos_2899_);
lean_ctor_set(v___x_2912_, 2, v_tk_2911_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2912_);
v___x_2914_ = v___x_2903_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_parserCache_2901_);
v___x_2914_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 3, v___x_2914_);
v___x_2916_ = v___x_2909_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_stxStack_2897_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_lhsPrec_2898_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_pos_2899_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_errorMsg_2896_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v_recoveredErrors_2900_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_del_object(v___x_2903_);
lean_dec_ref(v_parserCache_2901_);
lean_dec(v_startPos_2893_);
return v_s_2894_;
}
}
}
else
{
lean_dec_ref(v_cache_2895_);
lean_dec(v_startPos_2893_);
return v_s_2894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2928_, lean_object* v_c_2929_, lean_object* v_s_2930_){
_start:
{
lean_object* v_pos_2931_; lean_object* v_cache_2932_; lean_object* v_toInputContext_2933_; uint8_t v___x_2934_; 
v_pos_2931_ = lean_ctor_get(v_s_2930_, 2);
v_cache_2932_ = lean_ctor_get(v_s_2930_, 3);
v_toInputContext_2933_ = lean_ctor_get(v_c_2929_, 0);
v___x_2934_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2933_, v_pos_2931_);
if (v___x_2934_ == 0)
{
lean_object* v_tokenCache_2935_; lean_object* v_startPos_2936_; lean_object* v_stopPos_2937_; lean_object* v_token_2938_; uint8_t v___x_2939_; 
lean_dec(v_expected_2928_);
v_tokenCache_2935_ = lean_ctor_get(v_cache_2932_, 0);
v_startPos_2936_ = lean_ctor_get(v_tokenCache_2935_, 0);
v_stopPos_2937_ = lean_ctor_get(v_tokenCache_2935_, 1);
v_token_2938_ = lean_ctor_get(v_tokenCache_2935_, 2);
v___x_2939_ = lean_nat_dec_eq(v_startPos_2936_, v_pos_2931_);
if (v___x_2939_ == 0)
{
lean_object* v_s_2940_; lean_object* v___x_2941_; 
lean_inc(v_pos_2931_);
v_s_2940_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2929_, v_s_2930_);
v___x_2941_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2931_, v_s_2940_);
return v___x_2941_;
}
else
{
lean_object* v_s_2942_; lean_object* v___x_2943_; 
lean_inc(v_token_2938_);
lean_inc(v_stopPos_2937_);
lean_dec_ref(v_c_2929_);
v_s_2942_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2930_, v_token_2938_);
v___x_2943_ = l_Lean_Parser_ParserState_setPos(v_s_2942_, v_stopPos_2937_);
return v___x_2943_;
}
}
else
{
lean_object* v___x_2944_; 
lean_dec_ref(v_c_2929_);
v___x_2944_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2930_, v_expected_2928_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2945_, lean_object* v_s_2946_){
_start:
{
lean_object* v_pos_2947_; lean_object* v_iniSz_2948_; lean_object* v___x_2949_; lean_object* v_s_2950_; lean_object* v_errorMsg_2951_; 
v_pos_2947_ = lean_ctor_get(v_s_2946_, 2);
lean_inc(v_pos_2947_);
v_iniSz_2948_ = l_Lean_Parser_ParserState_stackSize(v_s_2946_);
v___x_2949_ = lean_box(0);
v_s_2950_ = l_Lean_Parser_tokenFn(v___x_2949_, v_c_2945_, v_s_2946_);
v_errorMsg_2951_ = lean_ctor_get(v_s_2950_, 4);
lean_inc(v_errorMsg_2951_);
if (lean_obj_tag(v_errorMsg_2951_) == 1)
{
lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2960_; 
v_isSharedCheck_2960_ = !lean_is_exclusive(v_errorMsg_2951_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_errorMsg_2951_, 0);
lean_dec(v_unused_2961_);
v___x_2953_ = v_errorMsg_2951_;
v_isShared_2954_ = v_isSharedCheck_2960_;
goto v_resetjp_2952_;
}
else
{
lean_dec(v_errorMsg_2951_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2960_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_inc_ref(v_s_2950_);
v___x_2955_ = l_Lean_Parser_ParserState_restore(v_s_2950_, v_iniSz_2948_, v_pos_2947_);
lean_dec(v_iniSz_2948_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 0);
lean_ctor_set(v___x_2953_, 0, v_s_2950_);
v___x_2957_ = v___x_2953_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_s_2950_);
v___x_2957_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2955_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
return v___x_2958_;
}
}
}
else
{
lean_object* v_stxStack_2962_; lean_object* v_stx_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_dec(v_errorMsg_2951_);
v_stxStack_2962_ = lean_ctor_get(v_s_2950_, 0);
lean_inc_ref(v_stxStack_2962_);
v_stx_2963_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2962_);
lean_dec_ref(v_stxStack_2962_);
v___x_2964_ = l_Lean_Parser_ParserState_restore(v_s_2950_, v_iniSz_2948_, v_pos_2947_);
lean_dec(v_iniSz_2948_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_stx_2963_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
return v___x_2966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2967_, lean_object* v_s_2968_){
_start:
{
lean_object* v_cache_2969_; lean_object* v_tokenCache_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2983_; 
v_cache_2969_ = lean_ctor_get(v_s_2968_, 3);
lean_inc_ref(v_cache_2969_);
v_tokenCache_2970_ = lean_ctor_get(v_cache_2969_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_cache_2969_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_cache_2969_, 1);
lean_dec(v_unused_2984_);
v___x_2972_ = v_cache_2969_;
v_isShared_2973_ = v_isSharedCheck_2983_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_tokenCache_2970_);
lean_dec(v_cache_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2983_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_pos_2974_; lean_object* v_startPos_2975_; lean_object* v_token_2976_; uint8_t v___x_2977_; 
v_pos_2974_ = lean_ctor_get(v_s_2968_, 2);
v_startPos_2975_ = lean_ctor_get(v_tokenCache_2970_, 0);
lean_inc(v_startPos_2975_);
v_token_2976_ = lean_ctor_get(v_tokenCache_2970_, 2);
lean_inc(v_token_2976_);
lean_dec_ref(v_tokenCache_2970_);
v___x_2977_ = lean_nat_dec_eq(v_startPos_2975_, v_pos_2974_);
lean_dec(v_startPos_2975_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_token_2976_);
lean_del_object(v___x_2972_);
v___x_2978_ = l_Lean_Parser_peekTokenAux(v_c_2967_, v_s_2968_);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
lean_dec_ref(v_c_2967_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_token_2976_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 1, v___x_2979_);
lean_ctor_set(v___x_2972_, 0, v_s_2968_);
v___x_2981_ = v___x_2972_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_s_2968_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2985_, lean_object* v_c_2986_, lean_object* v_s_2987_){
_start:
{
lean_object* v_pos_2988_; lean_object* v_toInputContext_2989_; uint8_t v___x_2990_; 
v_pos_2988_ = lean_ctor_get(v_s_2987_, 2);
v_toInputContext_2989_ = lean_ctor_get(v_c_2986_, 0);
v___x_2990_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2989_, v_pos_2988_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_inc(v_pos_2988_);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_box(0);
v___x_2993_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2988_, v___x_2991_, v_includeWhitespace_2985_, v___x_2992_, v_c_2986_, v_s_2987_);
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec_ref(v_c_2986_);
v___x_2994_ = lean_box(0);
v___x_2995_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2987_, v___x_2994_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2996_, lean_object* v_c_2997_, lean_object* v_s_2998_){
_start:
{
uint8_t v_includeWhitespace_boxed_2999_; lean_object* v_res_3000_; 
v_includeWhitespace_boxed_2999_ = lean_unbox(v_includeWhitespace_2996_);
v_res_3000_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2999_, v_c_2997_, v_s_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_3001_, lean_object* v_expected_3002_, lean_object* v_c_3003_, lean_object* v_s_3004_){
_start:
{
lean_object* v_pos_3005_; lean_object* v_s_3006_; lean_object* v_stxStack_3007_; lean_object* v_errorMsg_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; uint8_t v___x_3011_; 
v_pos_3005_ = lean_ctor_get(v_s_3004_, 2);
lean_inc(v_pos_3005_);
lean_inc(v_expected_3002_);
v_s_3006_ = l_Lean_Parser_tokenFn(v_expected_3002_, v_c_3003_, v_s_3004_);
v_stxStack_3007_ = lean_ctor_get(v_s_3006_, 0);
lean_inc_ref(v_stxStack_3007_);
v_errorMsg_3008_ = lean_ctor_get(v_s_3006_, 4);
lean_inc(v_errorMsg_3008_);
v___x_3009_ = lean_box(0);
v___x_3010_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3008_, v___x_3009_);
v___x_3011_ = lean_bool_not(v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3007_);
lean_dec_ref(v_stxStack_3007_);
if (lean_obj_tag(v___x_3012_) == 2)
{
lean_object* v_val_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_val_3013_ = lean_ctor_get(v___x_3012_, 1);
lean_inc_ref(v_val_3013_);
lean_dec_ref_known(v___x_3012_, 2);
v___x_3014_ = lean_apply_1(v_p_3001_, v_val_3013_);
v___x_3015_ = lean_unbox(v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3006_, v_expected_3002_, v_pos_3005_);
return v___x_3016_;
}
else
{
lean_dec(v_pos_3005_);
lean_dec(v_expected_3002_);
return v_s_3006_;
}
}
else
{
lean_object* v___x_3017_; 
lean_dec(v___x_3012_);
lean_dec_ref(v_p_3001_);
v___x_3017_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3006_, v_expected_3002_, v_pos_3005_);
return v___x_3017_;
}
}
else
{
lean_dec_ref(v_stxStack_3007_);
lean_dec(v_pos_3005_);
lean_dec(v_expected_3002_);
lean_dec_ref(v_p_3001_);
return v_s_3006_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_3018_, lean_object* v_s_3019_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_string_dec_eq(v_s_3019_, v_sym_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_3021_, lean_object* v_s_3022_){
_start:
{
uint8_t v_res_3023_; lean_object* v_r_3024_; 
v_res_3023_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_3021_, v_s_3022_);
lean_dec_ref(v_s_3022_);
lean_dec_ref(v_sym_3021_);
v_r_3024_ = lean_box(v_res_3023_);
return v_r_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_3025_, lean_object* v_errorMsg_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v___f_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___f_3029_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3029_, 0, v_sym_3025_);
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3031_, 0, v_errorMsg_3026_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = l_Lean_Parser_satisfySymbolFn(v___f_3029_, v___x_3031_, v_a_3027_, v_a_3028_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_3033_, lean_object* v_tks_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3035_, 0, v_sym_3033_);
lean_ctor_set(v___x_3035_, 1, v_tks_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_3036_){
_start:
{
lean_object* v___f_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_inc_ref(v_sym_3036_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3037_, 0, v_sym_3036_);
v___f_3038_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3040_, 0, v_sym_3036_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
v___x_3042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___f_3037_);
lean_ctor_set(v___x_3042_, 1, v___f_3038_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3047_ = lean_string_append(v___x_3046_, v_sym_3043_);
v___x_3048_ = lean_string_append(v___x_3047_, v___x_3046_);
v___x_3049_ = l_Lean_Parser_symbolFnAux(v_sym_3043_, v___x_3048_, v_a_3044_, v_a_3045_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_str_3055_; lean_object* v_startInclusive_3056_; lean_object* v_endExclusive_3057_; lean_object* v_sym_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3051_ = lean_unsigned_to_nat(0u);
v___x_3052_ = lean_string_utf8_byte_size(v_sym_3050_);
v___x_3053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3053_, 0, v_sym_3050_);
lean_ctor_set(v___x_3053_, 1, v___x_3051_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
v___x_3054_ = l_String_Slice_trimAscii(v___x_3053_);
v_str_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc_ref(v_str_3055_);
v_startInclusive_3056_ = lean_ctor_get(v___x_3054_, 1);
lean_inc(v_startInclusive_3056_);
v_endExclusive_3057_ = lean_ctor_get(v___x_3054_, 2);
lean_inc(v_endExclusive_3057_);
lean_dec_ref(v___x_3054_);
v_sym_3058_ = lean_string_utf8_extract(v_str_3055_, v_startInclusive_3056_, v_endExclusive_3057_);
lean_dec(v_endExclusive_3057_);
lean_dec(v_startInclusive_3056_);
lean_dec_ref(v_str_3055_);
lean_inc_ref(v_sym_3058_);
v___x_3059_ = l_Lean_Parser_symbolInfo(v_sym_3058_);
v___x_3060_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3060_, 0, v_sym_3058_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3062_, lean_object* v_errorMsg_3063_, lean_object* v_c_3064_, lean_object* v_s_3065_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v_s_3068_; lean_object* v_stxStack_3072_; lean_object* v_errorMsg_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3066_ = lean_box(0);
lean_inc_ref(v_errorMsg_3063_);
v___x_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_errorMsg_3063_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v_s_3068_ = l_Lean_Parser_tokenFn(v___x_3067_, v_c_3064_, v_s_3065_);
v_stxStack_3072_ = lean_ctor_get(v_s_3068_, 0);
lean_inc_ref(v_stxStack_3072_);
v_errorMsg_3073_ = lean_ctor_get(v_s_3068_, 4);
lean_inc(v_errorMsg_3073_);
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3073_, v___x_3074_);
v___x_3076_ = lean_bool_not(v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3072_);
lean_dec_ref(v_stxStack_3072_);
switch(lean_obj_tag(v___x_3077_))
{
case 2:
{
lean_object* v_val_3078_; uint8_t v___x_3079_; 
v_val_3078_ = lean_ctor_get(v___x_3077_, 1);
lean_inc_ref(v_val_3078_);
lean_dec_ref_known(v___x_3077_, 2);
v___x_3079_ = lean_string_dec_eq(v_sym_3062_, v_val_3078_);
lean_dec_ref(v_val_3078_);
lean_dec_ref(v_sym_3062_);
if (v___x_3079_ == 0)
{
goto v___jp_3069_;
}
else
{
lean_dec_ref(v_errorMsg_3063_);
return v_s_3068_;
}
}
case 3:
{
lean_object* v_rawVal_3080_; lean_object* v_info_3081_; lean_object* v_str_3082_; lean_object* v_startPos_3083_; lean_object* v_stopPos_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_rawVal_3080_ = lean_ctor_get(v___x_3077_, 1);
lean_inc_ref(v_rawVal_3080_);
v_info_3081_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_info_3081_);
lean_dec_ref_known(v___x_3077_, 4);
v_str_3082_ = lean_ctor_get(v_rawVal_3080_, 0);
lean_inc_ref(v_str_3082_);
v_startPos_3083_ = lean_ctor_get(v_rawVal_3080_, 1);
lean_inc(v_startPos_3083_);
v_stopPos_3084_ = lean_ctor_get(v_rawVal_3080_, 2);
lean_inc(v_stopPos_3084_);
lean_dec_ref(v_rawVal_3080_);
v___x_3085_ = lean_string_utf8_extract(v_str_3082_, v_startPos_3083_, v_stopPos_3084_);
lean_dec(v_stopPos_3084_);
lean_dec(v_startPos_3083_);
lean_dec_ref(v_str_3082_);
v___x_3086_ = lean_string_dec_eq(v_sym_3062_, v___x_3085_);
lean_dec_ref(v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec(v_info_3081_);
lean_dec_ref(v_sym_3062_);
goto v___jp_3069_;
}
else
{
lean_object* v_s_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec_ref(v_errorMsg_3063_);
v_s_3087_ = l_Lean_Parser_ParserState_popSyntax(v_s_3068_);
v___x_3088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_info_3081_);
lean_ctor_set(v___x_3088_, 1, v_sym_3062_);
v___x_3089_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3087_, v___x_3088_);
return v___x_3089_;
}
}
default: 
{
lean_dec(v___x_3077_);
lean_dec_ref(v_sym_3062_);
goto v___jp_3069_;
}
}
}
else
{
lean_dec_ref(v_stxStack_3072_);
lean_dec_ref(v_errorMsg_3063_);
lean_dec_ref(v_sym_3062_);
return v_s_3068_;
}
v___jp_3069_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_unsigned_to_nat(0u);
v___x_3071_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3068_, v_errorMsg_3063_, v___x_3070_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3093_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3094_ = lean_string_append(v___x_3093_, v_sym_3090_);
v___x_3095_ = lean_string_append(v___x_3094_, v___x_3093_);
v___x_3096_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3090_, v___x_3095_, v_a_3091_, v_a_3092_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3101_, uint8_t v_includeIdent_3102_){
_start:
{
lean_object* v___f_3103_; lean_object* v___f_3104_; 
v___f_3103_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3104_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3102_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3105_ = lean_box(0);
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_sym_3101_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___f_3103_);
lean_ctor_set(v___x_3108_, 1, v___f_3104_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3109_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3110_, 0, v_sym_3101_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
v___x_3112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3112_, 0, v___f_3103_);
lean_ctor_set(v___x_3112_, 1, v___f_3104_);
lean_ctor_set(v___x_3112_, 2, v___x_3111_);
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3113_, lean_object* v_includeIdent_3114_){
_start:
{
uint8_t v_includeIdent_boxed_3115_; lean_object* v_res_3116_; 
v_includeIdent_boxed_3115_ = lean_unbox(v_includeIdent_3114_);
v_res_3116_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3113_, v_includeIdent_boxed_3115_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3117_, uint8_t v_includeIdent_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v_str_3123_; lean_object* v_startInclusive_3124_; lean_object* v_endExclusive_3125_; lean_object* v_sym_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = lean_string_utf8_byte_size(v_sym_3117_);
v___x_3121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3121_, 0, v_sym_3117_);
lean_ctor_set(v___x_3121_, 1, v___x_3119_);
lean_ctor_set(v___x_3121_, 2, v___x_3120_);
v___x_3122_ = l_String_Slice_trimAscii(v___x_3121_);
v_str_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc_ref(v_str_3123_);
v_startInclusive_3124_ = lean_ctor_get(v___x_3122_, 1);
lean_inc(v_startInclusive_3124_);
v_endExclusive_3125_ = lean_ctor_get(v___x_3122_, 2);
lean_inc(v_endExclusive_3125_);
lean_dec_ref(v___x_3122_);
v_sym_3126_ = lean_string_utf8_extract(v_str_3123_, v_startInclusive_3124_, v_endExclusive_3125_);
lean_dec(v_endExclusive_3125_);
lean_dec(v_startInclusive_3124_);
lean_dec_ref(v_str_3123_);
lean_inc_ref(v_sym_3126_);
v___x_3127_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3126_, v_includeIdent_3118_);
v___x_3128_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3128_, 0, v_sym_3126_);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3130_, lean_object* v_includeIdent_3131_){
_start:
{
uint8_t v_includeIdent_boxed_3132_; lean_object* v_res_3133_; 
v_includeIdent_boxed_3132_ = lean_unbox(v_includeIdent_3131_);
v_res_3133_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3130_, v_includeIdent_boxed_3132_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3134_, lean_object* v_errorMsg_3135_, lean_object* v_j_3136_, lean_object* v_c_3137_, lean_object* v_s_3138_){
_start:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_string_utf8_at_end(v_sym_3134_, v_j_3136_);
if (v___x_3139_ == 0)
{
lean_object* v_pos_3140_; lean_object* v_toInputContext_3141_; uint8_t v___x_3142_; 
v_pos_3140_ = lean_ctor_get(v_s_3138_, 2);
v_toInputContext_3141_ = lean_ctor_get(v_c_3137_, 0);
v___x_3142_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3141_, v_pos_3140_);
if (v___x_3142_ == 0)
{
lean_object* v_inputString_3143_; uint32_t v___x_3144_; uint32_t v___x_3145_; uint8_t v___x_3146_; uint8_t v___x_3147_; 
v_inputString_3143_ = lean_ctor_get(v_toInputContext_3141_, 0);
v___x_3144_ = lean_string_utf8_get_fast(v_sym_3134_, v_j_3136_);
v___x_3145_ = lean_string_utf8_get_fast(v_inputString_3143_, v_pos_3140_);
v___x_3146_ = lean_uint32_dec_eq(v___x_3144_, v___x_3145_);
v___x_3147_ = lean_bool_not(v___x_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_inc(v_pos_3140_);
v___x_3148_ = lean_string_utf8_next_fast(v_sym_3134_, v_j_3136_);
lean_dec(v_j_3136_);
v___x_3149_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3138_, v_c_3137_, v_pos_3140_);
lean_dec(v_pos_3140_);
v_j_3136_ = v___x_3148_;
v_s_3138_ = v___x_3149_;
goto _start;
}
else
{
lean_object* v___x_3151_; 
lean_dec(v_j_3136_);
v___x_3151_ = l_Lean_Parser_ParserState_mkError(v_s_3138_, v_errorMsg_3135_);
return v___x_3151_;
}
}
else
{
lean_object* v___x_3152_; 
lean_dec(v_j_3136_);
v___x_3152_ = l_Lean_Parser_ParserState_mkError(v_s_3138_, v_errorMsg_3135_);
return v___x_3152_;
}
}
else
{
lean_dec(v_j_3136_);
lean_dec_ref(v_errorMsg_3135_);
return v_s_3138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3153_, lean_object* v_errorMsg_3154_, lean_object* v_j_3155_, lean_object* v_c_3156_, lean_object* v_s_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3153_, v_errorMsg_3154_, v_j_3155_, v_c_3156_, v_s_3157_);
lean_dec_ref(v_c_3156_);
lean_dec_ref(v_sym_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3159_, lean_object* v_errorMsg_3160_, lean_object* v_j_3161_, lean_object* v_c_3162_, lean_object* v_s_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3159_, v_errorMsg_3160_, v_j_3161_, v_c_3162_, v_s_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3165_, lean_object* v_errorMsg_3166_, lean_object* v_j_3167_, lean_object* v_c_3168_, lean_object* v_s_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Parser_strAux(v_sym_3165_, v_errorMsg_3166_, v_j_3167_, v_c_3168_, v_s_3169_);
lean_dec_ref(v_c_3168_);
lean_dec_ref(v_sym_3165_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3171_, lean_object* v_i_3172_){
_start:
{
lean_object* v_zero_3173_; uint8_t v_isZero_3174_; 
v_zero_3173_ = lean_unsigned_to_nat(0u);
v_isZero_3174_ = lean_nat_dec_eq(v_i_3172_, v_zero_3173_);
if (v_isZero_3174_ == 1)
{
lean_object* v___x_3175_; 
lean_dec(v_i_3172_);
v___x_3175_ = lean_box(0);
return v___x_3175_;
}
else
{
lean_object* v_one_3176_; lean_object* v_n_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; uint8_t v___x_3180_; 
v_one_3176_ = lean_unsigned_to_nat(1u);
v_n_3177_ = lean_nat_sub(v_i_3172_, v_one_3176_);
lean_dec(v_i_3172_);
v___x_3178_ = l_Subarray_get___redArg(v_as_3171_, v_n_3177_);
v___x_3179_ = l_Lean_Syntax_isNone(v___x_3178_);
v___x_3180_ = lean_bool_not(v___x_3179_);
if (v___x_3180_ == 0)
{
lean_dec(v___x_3178_);
v_i_3172_ = v_n_3177_;
goto _start;
}
else
{
lean_object* v___x_3182_; 
lean_dec(v_n_3177_);
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3178_);
return v___x_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3183_, lean_object* v_i_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3183_, v_i_3184_);
lean_dec_ref(v_as_3183_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3186_){
_start:
{
lean_object* v___x_3187_; lean_object* v_start_3188_; lean_object* v_stop_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3187_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3186_);
v_start_3188_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_start_3188_);
v_stop_3189_ = lean_ctor_get(v___x_3187_, 2);
lean_inc(v_stop_3189_);
v___x_3190_ = lean_nat_sub(v_stop_3189_, v_start_3188_);
lean_dec(v_start_3188_);
lean_dec(v_stop_3189_);
v___x_3191_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3187_, v___x_3190_);
lean_dec_ref(v___x_3187_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_box(0);
return v___x_3192_;
}
else
{
lean_object* v_val_3193_; 
v_val_3193_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_val_3193_);
lean_dec_ref_known(v___x_3191_, 1);
return v_val_3193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3194_, lean_object* v_i_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3194_, v_i_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3198_, lean_object* v_i_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3198_, v_i_3199_, v_a_3200_);
lean_dec_ref(v_as_3198_);
return v_res_3201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Syntax_getTailInfo(v_prev_3202_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_trailing_3204_; lean_object* v_startPos_3205_; lean_object* v_stopPos_3206_; uint8_t v___x_3207_; 
v_trailing_3204_ = lean_ctor_get(v___x_3203_, 2);
lean_inc_ref(v_trailing_3204_);
lean_dec_ref_known(v___x_3203_, 4);
v_startPos_3205_ = lean_ctor_get(v_trailing_3204_, 1);
lean_inc(v_startPos_3205_);
v_stopPos_3206_ = lean_ctor_get(v_trailing_3204_, 2);
lean_inc(v_stopPos_3206_);
lean_dec_ref(v_trailing_3204_);
v___x_3207_ = lean_nat_dec_lt(v_startPos_3205_, v_stopPos_3206_);
lean_dec(v_stopPos_3206_);
lean_dec(v_startPos_3205_);
return v___x_3207_;
}
else
{
uint8_t v___x_3208_; 
lean_dec(v___x_3203_);
v___x_3208_ = 0;
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = l_Lean_Parser_checkTailWs(v_prev_3209_);
lean_dec(v_prev_3209_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3212_, lean_object* v_s_3213_){
_start:
{
lean_object* v_stxStack_3214_; lean_object* v_prev_3215_; uint8_t v___x_3216_; 
v_stxStack_3214_ = lean_ctor_get(v_s_3213_, 0);
lean_inc_ref(v_stxStack_3214_);
v_prev_3215_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3214_);
v___x_3216_ = l_Lean_Parser_checkTailWs(v_prev_3215_);
lean_dec(v_prev_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Parser_ParserState_mkError(v_s_3213_, v_errorMsg_3212_);
return v___x_3217_;
}
else
{
lean_dec_ref(v_errorMsg_3212_);
return v_s_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3218_, lean_object* v_x_3219_, lean_object* v_s_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3218_, v_s_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3222_, lean_object* v_x_3223_, lean_object* v_s_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3222_, v_x_3223_, v_s_3224_);
lean_dec_ref(v_x_3223_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3226_){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3228_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3228_, 0, v_errorMsg_3226_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3227_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3238_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3239_ = l_Lean_addBuiltinDocString(v___x_3237_, v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3242_){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = l_String_instInhabitedSlice;
v___x_3244_ = lean_panic_fn_borrowed(v___x_3243_, v_msg_3242_);
return v___x_3244_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3245_, lean_object* v_a_3246_, uint8_t v_b_3247_){
_start:
{
lean_object* v_str_3248_; lean_object* v_startInclusive_3249_; lean_object* v_endExclusive_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v_str_3248_ = lean_ctor_get(v_s_3245_, 0);
v_startInclusive_3249_ = lean_ctor_get(v_s_3245_, 1);
v_endExclusive_3250_ = lean_ctor_get(v_s_3245_, 2);
v___x_3251_ = lean_nat_sub(v_endExclusive_3250_, v_startInclusive_3249_);
v___x_3252_ = lean_nat_dec_eq(v_a_3246_, v___x_3251_);
lean_dec(v___x_3251_);
if (v___x_3252_ == 0)
{
uint32_t v___x_3253_; lean_object* v___x_3254_; uint32_t v___x_3255_; uint8_t v___x_3256_; 
v___x_3253_ = 10;
v___x_3254_ = lean_nat_add(v_startInclusive_3249_, v_a_3246_);
lean_dec(v_a_3246_);
v___x_3255_ = lean_string_utf8_get_fast(v_str_3248_, v___x_3254_);
v___x_3256_ = lean_uint32_dec_eq(v___x_3255_, v___x_3253_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = lean_string_utf8_next_fast(v_str_3248_, v___x_3254_);
lean_dec(v___x_3254_);
v___x_3258_ = lean_nat_sub(v___x_3257_, v_startInclusive_3249_);
v_a_3246_ = v___x_3258_;
v_b_3247_ = v___x_3256_;
goto _start;
}
else
{
lean_dec(v___x_3254_);
return v___x_3256_;
}
}
else
{
lean_dec(v_a_3246_);
return v_b_3247_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3260_, lean_object* v_a_3261_, lean_object* v_b_3262_){
_start:
{
uint8_t v_b_boxed_3263_; uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_b_boxed_3263_ = lean_unbox(v_b_3262_);
v_res_3264_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3260_, v_a_3261_, v_b_boxed_3263_);
lean_dec_ref(v_s_3260_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3266_){
_start:
{
lean_object* v_searcher_3267_; uint8_t v___x_3268_; uint8_t v___x_3269_; 
v_searcher_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = 0;
v___x_3269_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3266_, v_searcher_3267_, v___x_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3270_){
_start:
{
uint8_t v_res_3271_; lean_object* v_r_3272_; 
v_res_3271_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3270_);
lean_dec_ref(v_s_3270_);
v_r_3272_ = lean_box(v_res_3271_);
return v_r_3272_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3276_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3277_ = lean_unsigned_to_nat(14u);
v___x_3278_ = lean_unsigned_to_nat(22u);
v___x_3279_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3280_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3281_ = l_mkPanicMessageWithDecl(v___x_3280_, v___x_3279_, v___x_3278_, v___x_3277_, v___x_3276_);
return v___x_3281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3282_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_Syntax_getTailInfo(v_prev_3282_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_trailing_3288_; lean_object* v_str_3289_; lean_object* v_startPos_3290_; lean_object* v_stopPos_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3302_; 
v_trailing_3288_ = lean_ctor_get(v___x_3287_, 2);
lean_inc_ref(v_trailing_3288_);
lean_dec_ref_known(v___x_3287_, 4);
v_str_3289_ = lean_ctor_get(v_trailing_3288_, 0);
v_startPos_3290_ = lean_ctor_get(v_trailing_3288_, 1);
v_stopPos_3291_ = lean_ctor_get(v_trailing_3288_, 2);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_trailing_3288_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3293_ = v_trailing_3288_;
v_isShared_3294_ = v_isSharedCheck_3302_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_stopPos_3291_);
lean_inc(v_startPos_3290_);
lean_inc(v_str_3289_);
lean_dec(v_trailing_3288_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3302_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
uint8_t v___x_3295_; 
v___x_3295_ = lean_string_is_valid_pos(v_str_3289_, v_startPos_3290_);
if (v___x_3295_ == 0)
{
lean_del_object(v___x_3293_);
lean_dec(v_stopPos_3291_);
lean_dec(v_startPos_3290_);
lean_dec_ref(v_str_3289_);
goto v___jp_3283_;
}
else
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_string_is_valid_pos(v_str_3289_, v_stopPos_3291_);
if (v___x_3296_ == 0)
{
lean_del_object(v___x_3293_);
lean_dec(v_stopPos_3291_);
lean_dec(v_startPos_3290_);
lean_dec_ref(v_str_3289_);
goto v___jp_3283_;
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_nat_dec_le(v_startPos_3290_, v_stopPos_3291_);
if (v___x_3297_ == 0)
{
lean_del_object(v___x_3293_);
lean_dec(v_stopPos_3291_);
lean_dec(v_startPos_3290_);
lean_dec_ref(v_str_3289_);
goto v___jp_3283_;
}
else
{
lean_object* v___x_3299_; 
if (v_isShared_3294_ == 0)
{
v___x_3299_ = v___x_3293_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_str_3289_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_startPos_3290_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_stopPos_3291_);
v___x_3299_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
uint8_t v___x_3300_; 
v___x_3300_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3299_);
lean_dec_ref(v___x_3299_);
return v___x_3300_;
}
}
}
}
}
}
else
{
uint8_t v___x_3303_; 
lean_dec(v___x_3287_);
v___x_3303_ = 0;
return v___x_3303_;
}
v___jp_3283_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3284_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3285_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3284_);
v___x_3286_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3285_);
lean_dec_ref(v___x_3285_);
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3304_){
_start:
{
uint8_t v_res_3305_; lean_object* v_r_3306_; 
v_res_3305_ = l_Lean_Parser_checkTailLinebreak(v_prev_3304_);
lean_dec(v_prev_3304_);
v_r_3306_ = lean_box(v_res_3305_);
return v_r_3306_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3307_, lean_object* v_inst_3308_, lean_object* v_R_3309_, lean_object* v_a_3310_, uint8_t v_b_3311_, lean_object* v_c_3312_){
_start:
{
uint8_t v___x_3313_; 
v___x_3313_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3307_, v_a_3310_, v_b_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3314_, lean_object* v_inst_3315_, lean_object* v_R_3316_, lean_object* v_a_3317_, lean_object* v_b_3318_, lean_object* v_c_3319_){
_start:
{
uint8_t v_b_boxed_3320_; uint8_t v_res_3321_; lean_object* v_r_3322_; 
v_b_boxed_3320_ = lean_unbox(v_b_3318_);
v_res_3321_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3314_, v_inst_3315_, v_R_3316_, v_a_3317_, v_b_boxed_3320_, v_c_3319_);
lean_dec_ref(v_s_3314_);
v_r_3322_ = lean_box(v_res_3321_);
return v_r_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3323_, lean_object* v_s_3324_){
_start:
{
lean_object* v_stxStack_3325_; lean_object* v_prev_3326_; uint8_t v___x_3327_; 
v_stxStack_3325_ = lean_ctor_get(v_s_3324_, 0);
v_prev_3326_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3325_);
v___x_3327_ = l_Lean_Parser_checkTailLinebreak(v_prev_3326_);
lean_dec(v_prev_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_Parser_ParserState_mkError(v_s_3324_, v_errorMsg_3323_);
return v___x_3328_;
}
else
{
lean_dec_ref(v_errorMsg_3323_);
return v_s_3324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3329_, lean_object* v_x_3330_, lean_object* v_s_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3329_, v_s_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3333_, lean_object* v_x_3334_, lean_object* v_s_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3333_, v_x_3334_, v_s_3335_);
lean_dec_ref(v_x_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3337_){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3339_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3339_, 0, v_errorMsg_3337_);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3349_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3350_ = l_Lean_addBuiltinDocString(v___x_3348_, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3352_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Syntax_getTailInfo(v_prev_3353_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_trailing_3355_; lean_object* v_startPos_3356_; lean_object* v_stopPos_3357_; uint8_t v___x_3358_; 
v_trailing_3355_ = lean_ctor_get(v___x_3354_, 2);
lean_inc_ref(v_trailing_3355_);
lean_dec_ref_known(v___x_3354_, 4);
v_startPos_3356_ = lean_ctor_get(v_trailing_3355_, 1);
lean_inc(v_startPos_3356_);
v_stopPos_3357_ = lean_ctor_get(v_trailing_3355_, 2);
lean_inc(v_stopPos_3357_);
lean_dec_ref(v_trailing_3355_);
v___x_3358_ = lean_nat_dec_eq(v_stopPos_3357_, v_startPos_3356_);
lean_dec(v_startPos_3356_);
lean_dec(v_stopPos_3357_);
return v___x_3358_;
}
else
{
uint8_t v___x_3359_; 
lean_dec(v___x_3354_);
v___x_3359_ = 0;
return v___x_3359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3360_){
_start:
{
uint8_t v_res_3361_; lean_object* v_r_3362_; 
v_res_3361_ = l_Lean_Parser_checkTailNoWs(v_prev_3360_);
lean_dec(v_prev_3360_);
v_r_3362_ = lean_box(v_res_3361_);
return v_r_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3363_, lean_object* v_s_3364_){
_start:
{
lean_object* v_stxStack_3365_; lean_object* v_prev_3366_; uint8_t v___x_3367_; 
v_stxStack_3365_ = lean_ctor_get(v_s_3364_, 0);
lean_inc_ref(v_stxStack_3365_);
v_prev_3366_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3365_);
v___x_3367_ = l_Lean_Parser_checkTailNoWs(v_prev_3366_);
lean_dec(v_prev_3366_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Parser_ParserState_mkError(v_s_3364_, v_errorMsg_3363_);
return v___x_3368_;
}
else
{
lean_dec_ref(v_errorMsg_3363_);
return v_s_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3369_, lean_object* v_x_3370_, lean_object* v_s_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3369_, v_s_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3373_, lean_object* v_x_3374_, lean_object* v_s_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3373_, v_x_3374_, v_s_3375_);
lean_dec_ref(v_x_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3377_){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3378_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3379_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3379_, 0, v_errorMsg_3377_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3389_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3390_ = l_Lean_addBuiltinDocString(v___x_3388_, v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3393_, lean_object* v_asciiSym_3394_, lean_object* v_s_3395_){
_start:
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_string_dec_eq(v_s_3395_, v_sym_3393_);
if (v___x_3396_ == 0)
{
uint8_t v___x_3397_; 
v___x_3397_ = lean_string_dec_eq(v_s_3395_, v_asciiSym_3394_);
return v___x_3397_;
}
else
{
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3398_, lean_object* v_asciiSym_3399_, lean_object* v_s_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3398_, v_asciiSym_3399_, v_s_3400_);
lean_dec_ref(v_s_3400_);
lean_dec_ref(v_asciiSym_3399_);
lean_dec_ref(v_sym_3398_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3403_, lean_object* v_asciiSym_3404_, lean_object* v_expected_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___f_3408_; lean_object* v___x_3409_; 
v___f_3408_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3408_, 0, v_sym_3403_);
lean_closure_set(v___f_3408_, 1, v_asciiSym_3404_);
v___x_3409_ = l_Lean_Parser_satisfySymbolFn(v___f_3408_, v_expected_3405_, v_a_3406_, v_a_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3410_, lean_object* v_sym_3411_, lean_object* v_tks_3412_){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v_asciiSym_3410_);
lean_ctor_set(v___x_3413_, 1, v_tks_3412_);
v___x_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_sym_3411_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3415_, lean_object* v_asciiSym_3416_){
_start:
{
lean_object* v___f_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_inc_ref(v_sym_3415_);
lean_inc_ref(v_asciiSym_3416_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3417_, 0, v_asciiSym_3416_);
lean_closure_set(v___f_3417_, 1, v_sym_3415_);
v___f_3418_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v_asciiSym_3416_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_sym_3415_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
v___x_3423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3423_, 0, v___f_3417_);
lean_ctor_set(v___x_3423_, 1, v___f_3418_);
lean_ctor_set(v___x_3423_, 2, v___x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3425_, lean_object* v_asciiSym_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3429_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3430_ = lean_string_append(v___x_3429_, v_sym_3425_);
v___x_3431_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3432_ = lean_string_append(v___x_3430_, v___x_3431_);
v___x_3433_ = lean_string_append(v___x_3432_, v_asciiSym_3426_);
v___x_3434_ = lean_string_append(v___x_3433_, v___x_3429_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3434_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3425_, v_asciiSym_3426_, v___x_3436_, v_a_3427_, v_a_3428_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3438_, lean_object* v_asciiSym_3439_){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_str_3444_; lean_object* v_startInclusive_3445_; lean_object* v_endExclusive_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3463_; 
v___x_3440_ = lean_unsigned_to_nat(0u);
v___x_3441_ = lean_string_utf8_byte_size(v_sym_3438_);
v___x_3442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3442_, 0, v_sym_3438_);
lean_ctor_set(v___x_3442_, 1, v___x_3440_);
lean_ctor_set(v___x_3442_, 2, v___x_3441_);
v___x_3443_ = l_String_Slice_trimAscii(v___x_3442_);
v_str_3444_ = lean_ctor_get(v___x_3443_, 0);
v_startInclusive_3445_ = lean_ctor_get(v___x_3443_, 1);
v_endExclusive_3446_ = lean_ctor_get(v___x_3443_, 2);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3448_ = v___x_3443_;
v_isShared_3449_ = v_isSharedCheck_3463_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_endExclusive_3446_);
lean_inc(v_startInclusive_3445_);
lean_inc(v_str_3444_);
lean_dec(v___x_3443_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3463_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = lean_string_utf8_byte_size(v_asciiSym_3439_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 2, v___x_3450_);
lean_ctor_set(v___x_3448_, 1, v___x_3440_);
lean_ctor_set(v___x_3448_, 0, v_asciiSym_3439_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_asciiSym_3439_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; lean_object* v_str_3454_; lean_object* v_startInclusive_3455_; lean_object* v_endExclusive_3456_; lean_object* v_sym_3457_; lean_object* v_asciiSym_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3453_ = l_String_Slice_trimAscii(v___x_3452_);
v_str_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc_ref(v_str_3454_);
v_startInclusive_3455_ = lean_ctor_get(v___x_3453_, 1);
lean_inc(v_startInclusive_3455_);
v_endExclusive_3456_ = lean_ctor_get(v___x_3453_, 2);
lean_inc(v_endExclusive_3456_);
lean_dec_ref(v___x_3453_);
v_sym_3457_ = lean_string_utf8_extract(v_str_3444_, v_startInclusive_3445_, v_endExclusive_3446_);
lean_dec(v_endExclusive_3446_);
lean_dec(v_startInclusive_3445_);
lean_dec_ref(v_str_3444_);
v_asciiSym_3458_ = lean_string_utf8_extract(v_str_3454_, v_startInclusive_3455_, v_endExclusive_3456_);
lean_dec(v_endExclusive_3456_);
lean_dec(v_startInclusive_3455_);
lean_dec_ref(v_str_3454_);
lean_inc_ref(v_asciiSym_3458_);
lean_inc_ref(v_sym_3457_);
v___x_3459_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3457_, v_asciiSym_3458_);
v___x_3460_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3460_, 0, v_sym_3457_);
lean_closure_set(v___x_3460_, 1, v_asciiSym_3458_);
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
return v___x_3461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3464_, lean_object* v_asciiSym_3465_, uint8_t v_preserveForPP_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3464_, v_asciiSym_3465_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3468_, lean_object* v_asciiSym_3469_, lean_object* v_preserveForPP_3470_){
_start:
{
uint8_t v_preserveForPP_boxed_3471_; lean_object* v_res_3472_; 
v_preserveForPP_boxed_3471_ = lean_unbox(v_preserveForPP_3470_);
v_res_3472_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3468_, v_asciiSym_3469_, v_preserveForPP_boxed_3471_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3473_){
_start:
{
lean_object* v___f_3474_; lean_object* v___f_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___f_3474_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3475_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3477_, 0, v_k_3473_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
v___x_3479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3479_, 0, v___f_3474_);
lean_ctor_set(v___x_3479_, 1, v___f_3475_);
lean_ctor_set(v___x_3479_, 2, v___x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3480_, lean_object* v_desc_3481_, lean_object* v_c_3482_, lean_object* v_s_3483_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v_s_3486_; uint8_t v___y_3488_; lean_object* v_stxStack_3491_; lean_object* v_errorMsg_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; uint8_t v___x_3495_; uint8_t v___x_3496_; 
v___x_3484_ = lean_box(0);
lean_inc_ref(v_desc_3481_);
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_desc_3481_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v_s_3486_ = l_Lean_Parser_tokenFn(v___x_3485_, v_c_3482_, v_s_3483_);
v_stxStack_3491_ = lean_ctor_get(v_s_3486_, 0);
lean_inc_ref(v_stxStack_3491_);
v_errorMsg_3492_ = lean_ctor_get(v_s_3486_, 4);
lean_inc(v_errorMsg_3492_);
v___x_3493_ = lean_box(0);
v___x_3494_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3492_, v___x_3493_);
v___x_3495_ = lean_bool_not(v___x_3494_);
v___x_3496_ = lean_bool_not(v___x_3495_);
if (v___x_3496_ == 0)
{
lean_dec_ref(v_stxStack_3491_);
v___y_3488_ = v___x_3496_;
goto v___jp_3487_;
}
else
{
lean_object* v___x_3497_; uint8_t v___x_3498_; uint8_t v___x_3499_; 
v___x_3497_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3491_);
lean_dec_ref(v_stxStack_3491_);
v___x_3498_ = l_Lean_Syntax_isOfKind(v___x_3497_, v_k_3480_);
v___x_3499_ = lean_bool_not(v___x_3498_);
v___y_3488_ = v___x_3499_;
goto v___jp_3487_;
}
v___jp_3487_:
{
if (v___y_3488_ == 0)
{
lean_dec_ref(v_desc_3481_);
return v_s_3486_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3486_, v_desc_3481_, v___x_3489_);
return v___x_3490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3500_, lean_object* v_desc_3501_, lean_object* v_c_3502_, lean_object* v_s_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Parser_expectTokenFn(v_k_3500_, v_desc_3501_, v_c_3502_, v_s_3503_);
lean_dec(v_k_3500_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3508_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3509_ = l_Lean_Parser_expectTokenFn(v___x_3507_, v___x_3508_, v_a_3505_, v_a_3506_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3511_ = l_Lean_Parser_mkAtomicInfo(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3513_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3519_, lean_object* v_s_3520_){
_start:
{
lean_object* v_pos_3521_; uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_pos_3521_ = lean_ctor_get(v_s_3520_, 2);
lean_inc(v_pos_3521_);
v___x_3522_ = 1;
v___x_3523_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3524_ = l_Lean_Parser_hexNumberFn(v_pos_3521_, v___x_3522_, v___x_3523_, v_ctx_3519_, v_s_3520_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3526_ = l_Lean_Parser_mkAtomicInfo(v___x_3525_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3528_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3527_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3535_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3536_ = l_Lean_Parser_expectTokenFn(v___x_3534_, v___x_3535_, v_a_3532_, v_a_3533_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3538_ = l_Lean_Parser_mkAtomicInfo(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3540_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3547_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3548_ = l_Lean_Parser_expectTokenFn(v___x_3546_, v___x_3547_, v_a_3544_, v_a_3545_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3550_ = l_Lean_Parser_mkAtomicInfo(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3552_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
lean_ctor_set(v___x_3553_, 1, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3559_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3560_ = l_Lean_Parser_expectTokenFn(v___x_3558_, v___x_3559_, v_a_3556_, v_a_3557_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3562_ = l_Lean_Parser_mkAtomicInfo(v___x_3561_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3564_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3574_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3575_ = l_Lean_Parser_expectTokenFn(v___x_3573_, v___x_3574_, v_a_3571_, v_a_3572_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3577_ = l_Lean_Parser_mkAtomicInfo(v___x_3576_);
return v___x_3577_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3579_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___x_3578_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3587_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3588_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3589_ = l_Lean_Parser_expectTokenFn(v___x_3587_, v___x_3588_, v_a_3585_, v_a_3586_);
return v___x_3589_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3591_ = l_Lean_Parser_mkAtomicInfo(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3593_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v___x_3592_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3607_, lean_object* v_c_3608_, lean_object* v_s_3609_){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_s_3612_; lean_object* v_stxStack_3613_; lean_object* v_errorMsg_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3610_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3611_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3612_ = l_Lean_Parser_tokenFn(v___x_3611_, v_c_3608_, v_s_3609_);
v_stxStack_3613_ = lean_ctor_get(v_s_3612_, 0);
lean_inc_ref(v_stxStack_3613_);
v_errorMsg_3614_ = lean_ctor_get(v_s_3612_, 4);
lean_inc(v_errorMsg_3614_);
v___x_3615_ = lean_box(0);
v___x_3616_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3614_, v___x_3615_);
v___x_3617_ = lean_bool_not(v___x_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3613_);
lean_dec_ref(v_stxStack_3613_);
if (lean_obj_tag(v___x_3618_) == 3)
{
lean_object* v_val_3619_; uint8_t v___x_3620_; uint8_t v___x_3621_; 
v_val_3619_ = lean_ctor_get(v___x_3618_, 2);
lean_inc(v_val_3619_);
lean_dec_ref_known(v___x_3618_, 4);
v___x_3620_ = lean_name_eq(v_val_3619_, v_id_3607_);
lean_dec(v_val_3619_);
v___x_3621_ = lean_bool_not(v___x_3620_);
if (v___x_3621_ == 0)
{
lean_dec(v_id_3607_);
return v_s_3612_;
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3622_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3623_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3607_, v___x_3621_);
v___x_3624_ = lean_string_append(v___x_3622_, v___x_3623_);
lean_dec_ref(v___x_3623_);
v___x_3625_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3626_ = lean_string_append(v___x_3624_, v___x_3625_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3612_, v___x_3626_, v___x_3627_);
return v___x_3628_;
}
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_dec(v___x_3618_);
lean_dec(v_id_3607_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3612_, v___x_3610_, v___x_3629_);
return v___x_3630_;
}
}
else
{
lean_dec_ref(v_stxStack_3613_);
lean_dec(v_id_3607_);
return v_s_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3631_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3632_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3633_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3633_, 0, v_id_3631_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3632_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3638_, lean_object* v_s_3639_){
_start:
{
lean_object* v_pos_3641_; lean_object* v_str_3642_; lean_object* v_trailing_3643_; lean_object* v_s_3644_; lean_object* v_stxStack_3656_; lean_object* v_pos_3657_; uint8_t v___x_3660_; uint8_t v___x_3661_; 
v_stxStack_3656_ = lean_ctor_get(v_s_3639_, 0);
v_pos_3657_ = lean_ctor_get(v_s_3639_, 2);
v___x_3660_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3656_);
v___x_3661_ = lean_bool_not(v___x_3660_);
if (v___x_3661_ == 0)
{
lean_inc(v_pos_3657_);
goto v___jp_3658_;
}
else
{
lean_object* v_prev_3662_; lean_object* v___x_3663_; 
v_prev_3662_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3656_);
v___x_3663_ = l_Lean_Syntax_getTailInfo(v_prev_3662_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_leading_3664_; lean_object* v_pos_3665_; lean_object* v_trailing_3666_; lean_object* v_endPos_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3678_; 
v_leading_3664_ = lean_ctor_get(v___x_3663_, 0);
v_pos_3665_ = lean_ctor_get(v___x_3663_, 1);
v_trailing_3666_ = lean_ctor_get(v___x_3663_, 2);
v_endPos_3667_ = lean_ctor_get(v___x_3663_, 3);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3669_ = v___x_3663_;
v_isShared_3670_ = v_isSharedCheck_3678_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_endPos_3667_);
lean_inc(v_trailing_3666_);
lean_inc(v_pos_3665_);
lean_inc(v_leading_3664_);
lean_dec(v___x_3663_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3678_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_str_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
lean_inc_n(v_endPos_3667_, 2);
v_str_3671_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3638_, v_endPos_3667_);
v___x_3672_ = l_Lean_Parser_ParserState_popSyntax(v_s_3639_);
lean_inc_ref(v_str_3671_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 2, v_str_3671_);
v___x_3674_ = v___x_3669_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_leading_3664_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_pos_3665_);
lean_ctor_set(v_reuseFailAlloc_3677_, 2, v_str_3671_);
lean_ctor_set(v_reuseFailAlloc_3677_, 3, v_endPos_3667_);
v___x_3674_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; lean_object* v_s_3676_; 
v___x_3675_ = l_Lean_Syntax_setTailInfo(v_prev_3662_, v___x_3674_);
v_s_3676_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3672_, v___x_3675_);
v_pos_3641_ = v_endPos_3667_;
v_str_3642_ = v_str_3671_;
v_trailing_3643_ = v_trailing_3666_;
v_s_3644_ = v_s_3676_;
goto v___jp_3640_;
}
}
}
else
{
lean_inc(v_pos_3657_);
lean_dec(v___x_3663_);
lean_dec(v_prev_3662_);
goto v___jp_3658_;
}
}
v___jp_3640_:
{
lean_object* v_info_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v_ident_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_inc(v_pos_3641_);
lean_inc_ref(v_str_3642_);
v_info_3645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3645_, 0, v_str_3642_);
lean_ctor_set(v_info_3645_, 1, v_pos_3641_);
lean_ctor_set(v_info_3645_, 2, v_trailing_3643_);
lean_ctor_set(v_info_3645_, 3, v_pos_3641_);
v___x_3646_ = lean_box(0);
v___x_3647_ = lean_box(0);
v_ident_3648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3648_, 0, v_info_3645_);
lean_ctor_set(v_ident_3648_, 1, v_str_3642_);
lean_ctor_set(v_ident_3648_, 2, v___x_3646_);
lean_ctor_set(v_ident_3648_, 3, v___x_3647_);
v___x_3649_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3650_ = lean_unsigned_to_nat(1u);
v___x_3651_ = lean_mk_empty_array_with_capacity(v___x_3650_);
v___x_3652_ = lean_array_push(v___x_3651_, v_ident_3648_);
v___x_3653_ = lean_box(2);
v___x_3654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v___x_3649_);
lean_ctor_set(v___x_3654_, 2, v___x_3652_);
v___x_3655_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3644_, v___x_3654_);
return v___x_3655_;
}
v___jp_3658_:
{
lean_object* v_str_3659_; 
lean_inc(v_pos_3657_);
v_str_3659_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3638_, v_pos_3657_);
lean_inc_ref(v_str_3659_);
v_pos_3641_ = v_pos_3657_;
v_str_3642_ = v_str_3659_;
v_trailing_3643_ = v_str_3659_;
v_s_3644_ = v_s_3639_;
goto v___jp_3640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3679_, lean_object* v_s_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Parser_hygieneInfoFn(v_c_3679_, v_s_3680_);
lean_dec_ref(v_c_3679_);
return v_res_3681_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3683_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3684_ = l_Lean_Parser_nodeInfo(v___x_3683_, v___x_3682_);
return v___x_3684_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3686_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
lean_ctor_set(v___x_3687_, 1, v___x_3685_);
return v___x_3687_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3689_, lean_object* v_startStackSize_3690_){
_start:
{
lean_object* v_node_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_node_3691_ = l_Lean_Parser_SyntaxStack_back(v_s_3689_);
v___x_3692_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3689_, v_startStackSize_3690_);
v___x_3693_ = l_Lean_Parser_SyntaxStack_push(v___x_3692_, v_node_3691_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3694_, lean_object* v_startStackSize_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Parser_ParserState_keepTop(v_s_3694_, v_startStackSize_3695_);
lean_dec(v_startStackSize_3695_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3697_, lean_object* v_oldStackSize_3698_){
_start:
{
lean_object* v_stxStack_3699_; lean_object* v_lhsPrec_3700_; lean_object* v_pos_3701_; lean_object* v_cache_3702_; lean_object* v_errorMsg_3703_; lean_object* v_recoveredErrors_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3712_; 
v_stxStack_3699_ = lean_ctor_get(v_s_3697_, 0);
v_lhsPrec_3700_ = lean_ctor_get(v_s_3697_, 1);
v_pos_3701_ = lean_ctor_get(v_s_3697_, 2);
v_cache_3702_ = lean_ctor_get(v_s_3697_, 3);
v_errorMsg_3703_ = lean_ctor_get(v_s_3697_, 4);
v_recoveredErrors_3704_ = lean_ctor_get(v_s_3697_, 5);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_s_3697_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3706_ = v_s_3697_;
v_isShared_3707_ = v_isSharedCheck_3712_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_recoveredErrors_3704_);
lean_inc(v_errorMsg_3703_);
lean_inc(v_cache_3702_);
lean_inc(v_pos_3701_);
lean_inc(v_lhsPrec_3700_);
lean_inc(v_stxStack_3699_);
lean_dec(v_s_3697_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3712_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3708_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3699_, v_oldStackSize_3698_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3708_);
v___x_3710_ = v___x_3706_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_lhsPrec_3700_);
lean_ctor_set(v_reuseFailAlloc_3711_, 2, v_pos_3701_);
lean_ctor_set(v_reuseFailAlloc_3711_, 3, v_cache_3702_);
lean_ctor_set(v_reuseFailAlloc_3711_, 4, v_errorMsg_3703_);
lean_ctor_set(v_reuseFailAlloc_3711_, 5, v_recoveredErrors_3704_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3713_, lean_object* v_oldStackSize_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Parser_ParserState_keepNewError(v_s_3713_, v_oldStackSize_3714_);
lean_dec(v_oldStackSize_3714_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3716_, lean_object* v_oldStackSize_3717_, lean_object* v_oldStopPos_3718_, lean_object* v_oldError_3719_, lean_object* v_oldLhsPrec_3720_){
_start:
{
lean_object* v_stxStack_3721_; lean_object* v_cache_3722_; lean_object* v_recoveredErrors_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3731_; 
v_stxStack_3721_ = lean_ctor_get(v_s_3716_, 0);
v_cache_3722_ = lean_ctor_get(v_s_3716_, 3);
v_recoveredErrors_3723_ = lean_ctor_get(v_s_3716_, 5);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_s_3716_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; 
v_unused_3732_ = lean_ctor_get(v_s_3716_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_s_3716_, 2);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_s_3716_, 1);
lean_dec(v_unused_3734_);
v___x_3725_ = v_s_3716_;
v_isShared_3726_ = v_isSharedCheck_3731_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_recoveredErrors_3723_);
lean_inc(v_cache_3722_);
lean_inc(v_stxStack_3721_);
lean_dec(v_s_3716_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3731_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3727_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3721_, v_oldStackSize_3717_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 4, v_oldError_3719_);
lean_ctor_set(v___x_3725_, 2, v_oldStopPos_3718_);
lean_ctor_set(v___x_3725_, 1, v_oldLhsPrec_3720_);
lean_ctor_set(v___x_3725_, 0, v___x_3727_);
v___x_3729_ = v___x_3725_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_oldLhsPrec_3720_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_oldStopPos_3718_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_cache_3722_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_oldError_3719_);
lean_ctor_set(v_reuseFailAlloc_3730_, 5, v_recoveredErrors_3723_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3735_, lean_object* v_oldStackSize_3736_, lean_object* v_oldStopPos_3737_, lean_object* v_oldError_3738_, lean_object* v_oldLhsPrec_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3735_, v_oldStackSize_3736_, v_oldStopPos_3737_, v_oldError_3738_, v_oldLhsPrec_3739_);
lean_dec(v_oldStackSize_3736_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3741_, lean_object* v_oldStackSize_3742_, lean_object* v_oldError_3743_){
_start:
{
lean_object* v_stxStack_3744_; lean_object* v_lhsPrec_3745_; lean_object* v_pos_3746_; lean_object* v_cache_3747_; lean_object* v_errorMsg_3748_; lean_object* v_recoveredErrors_3749_; lean_object* v___y_3751_; 
v_stxStack_3744_ = lean_ctor_get(v_s_3741_, 0);
v_lhsPrec_3745_ = lean_ctor_get(v_s_3741_, 1);
v_pos_3746_ = lean_ctor_get(v_s_3741_, 2);
v_cache_3747_ = lean_ctor_get(v_s_3741_, 3);
v_errorMsg_3748_ = lean_ctor_get(v_s_3741_, 4);
v_recoveredErrors_3749_ = lean_ctor_get(v_s_3741_, 5);
if (lean_obj_tag(v_errorMsg_3748_) == 1)
{
lean_object* v_val_3755_; uint8_t v___x_3756_; 
lean_inc_ref(v_errorMsg_3748_);
lean_inc_ref(v_recoveredErrors_3749_);
lean_inc_ref(v_cache_3747_);
lean_inc(v_pos_3746_);
lean_inc(v_lhsPrec_3745_);
lean_inc_ref(v_stxStack_3744_);
lean_dec_ref(v_s_3741_);
v_val_3755_ = lean_ctor_get(v_errorMsg_3748_, 0);
lean_inc_n(v_val_3755_, 2);
lean_dec_ref_known(v_errorMsg_3748_, 1);
lean_inc_ref(v_oldError_3743_);
v___x_3756_ = l_Lean_Parser_instBEqError_beq(v_oldError_3743_, v_val_3755_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Parser_Error_merge(v_oldError_3743_, v_val_3755_);
v___y_3751_ = v___x_3757_;
goto v___jp_3750_;
}
else
{
lean_dec_ref(v_oldError_3743_);
v___y_3751_ = v_val_3755_;
goto v___jp_3750_;
}
}
else
{
lean_dec_ref(v_oldError_3743_);
return v_s_3741_;
}
v___jp_3750_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3744_, v_oldStackSize_3742_);
v___x_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___y_3751_);
v___x_3754_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v_lhsPrec_3745_);
lean_ctor_set(v___x_3754_, 2, v_pos_3746_);
lean_ctor_set(v___x_3754_, 3, v_cache_3747_);
lean_ctor_set(v___x_3754_, 4, v___x_3753_);
lean_ctor_set(v___x_3754_, 5, v_recoveredErrors_3749_);
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3758_, lean_object* v_oldStackSize_3759_, lean_object* v_oldError_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3758_, v_oldStackSize_3759_, v_oldError_3760_);
lean_dec(v_oldStackSize_3759_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3762_, lean_object* v_startStackSize_3763_){
_start:
{
lean_object* v_stxStack_3764_; lean_object* v_lhsPrec_3765_; lean_object* v_pos_3766_; lean_object* v_cache_3767_; lean_object* v_recoveredErrors_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3777_; 
v_stxStack_3764_ = lean_ctor_get(v_s_3762_, 0);
v_lhsPrec_3765_ = lean_ctor_get(v_s_3762_, 1);
v_pos_3766_ = lean_ctor_get(v_s_3762_, 2);
v_cache_3767_ = lean_ctor_get(v_s_3762_, 3);
v_recoveredErrors_3768_ = lean_ctor_get(v_s_3762_, 5);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_s_3762_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v_s_3762_, 4);
lean_dec(v_unused_3778_);
v___x_3770_ = v_s_3762_;
v_isShared_3771_ = v_isSharedCheck_3777_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_recoveredErrors_3768_);
lean_inc(v_cache_3767_);
lean_inc(v_pos_3766_);
lean_inc(v_lhsPrec_3765_);
lean_inc(v_stxStack_3764_);
lean_dec(v_s_3762_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3777_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3772_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3764_, v_startStackSize_3763_);
v___x_3773_ = lean_box(0);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 4, v___x_3773_);
lean_ctor_set(v___x_3770_, 0, v___x_3772_);
v___x_3775_ = v___x_3770_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_lhsPrec_3765_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_pos_3766_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v_cache_3767_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3776_, 5, v_recoveredErrors_3768_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3779_, lean_object* v_startStackSize_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_Parser_ParserState_keepLatest(v_s_3779_, v_startStackSize_3780_);
lean_dec(v_startStackSize_3780_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3782_, lean_object* v_startStackSize_3783_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lean_Parser_ParserState_keepLatest(v_s_3782_, v_startStackSize_3783_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3785_, lean_object* v_startStackSize_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3785_, v_startStackSize_3786_);
lean_dec(v_startStackSize_3786_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3789_){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3791_ = l_Lean_Parser_ParserState_mkError(v_s_3789_, v___x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3792_, lean_object* v_startLhsPrec_3793_, lean_object* v_p_3794_, lean_object* v_c_3795_, lean_object* v_s_3796_){
_start:
{
lean_object* v___y_3798_; lean_object* v_s_3799_; lean_object* v_stxStack_3813_; lean_object* v_pos_3814_; lean_object* v_cache_3815_; lean_object* v_errorMsg_3816_; lean_object* v_recoveredErrors_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3830_; 
v_stxStack_3813_ = lean_ctor_get(v_s_3796_, 0);
v_pos_3814_ = lean_ctor_get(v_s_3796_, 2);
v_cache_3815_ = lean_ctor_get(v_s_3796_, 3);
v_errorMsg_3816_ = lean_ctor_get(v_s_3796_, 4);
v_recoveredErrors_3817_ = lean_ctor_get(v_s_3796_, 5);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_s_3796_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v_s_3796_, 1);
lean_dec(v_unused_3831_);
v___x_3819_ = v_s_3796_;
v_isShared_3820_ = v_isSharedCheck_3830_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_recoveredErrors_3817_);
lean_inc(v_errorMsg_3816_);
lean_inc(v_cache_3815_);
lean_inc(v_pos_3814_);
lean_inc(v_stxStack_3813_);
lean_dec(v_s_3796_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3830_;
goto v_resetjp_3818_;
}
v___jp_3797_:
{
lean_object* v_s_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_s_3800_ = lean_apply_2(v_p_3794_, v_c_3795_, v_s_3799_);
v___x_3801_ = l_Lean_Parser_ParserState_stackSize(v_s_3800_);
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_nat_add(v___y_3798_, v___x_3802_);
v___x_3804_ = lean_nat_dec_eq(v___x_3801_, v___x_3803_);
lean_dec(v___x_3803_);
lean_dec(v___x_3801_);
if (v___x_3804_ == 0)
{
lean_object* v_errorMsg_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; uint8_t v___x_3808_; 
v_errorMsg_3805_ = lean_ctor_get(v_s_3800_, 4);
lean_inc(v_errorMsg_3805_);
v___x_3806_ = lean_box(0);
v___x_3807_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3805_, v___x_3806_);
v___x_3808_ = lean_bool_not(v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
lean_dec(v___y_3798_);
v___x_3809_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3800_);
return v___x_3809_;
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3800_, v___y_3798_);
lean_dec(v___y_3798_);
v___x_3811_ = lean_box(0);
v___x_3812_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3810_, v___x_3811_);
return v___x_3812_;
}
}
else
{
lean_dec(v___y_3798_);
return v_s_3800_;
}
}
v_resetjp_3818_:
{
lean_object* v___y_3822_; 
if (lean_obj_tag(v_left_x3f_3792_) == 0)
{
lean_object* v___x_3829_; 
lean_dec(v_startLhsPrec_3793_);
v___x_3829_ = l_Lean_Parser_maxPrec;
v___y_3822_ = v___x_3829_;
goto v___jp_3821_;
}
else
{
v___y_3822_ = v_startLhsPrec_3793_;
goto v___jp_3821_;
}
v___jp_3821_:
{
lean_object* v_s_3824_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 1, v___y_3822_);
v_s_3824_ = v___x_3819_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_stxStack_3813_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___y_3822_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v_pos_3814_);
lean_ctor_set(v_reuseFailAlloc_3828_, 3, v_cache_3815_);
lean_ctor_set(v_reuseFailAlloc_3828_, 4, v_errorMsg_3816_);
lean_ctor_set(v_reuseFailAlloc_3828_, 5, v_recoveredErrors_3817_);
v_s_3824_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v_startSize_3825_; 
v_startSize_3825_ = l_Lean_Parser_ParserState_stackSize(v_s_3824_);
if (lean_obj_tag(v_left_x3f_3792_) == 1)
{
lean_object* v_val_3826_; lean_object* v_s_3827_; 
v_val_3826_ = lean_ctor_get(v_left_x3f_3792_, 0);
lean_inc(v_val_3826_);
lean_dec_ref_known(v_left_x3f_3792_, 1);
v_s_3827_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3824_, v_val_3826_);
v___y_3798_ = v_startSize_3825_;
v_s_3799_ = v_s_3827_;
goto v___jp_3797_;
}
else
{
lean_dec(v_left_x3f_3792_);
v___y_3798_ = v_startSize_3825_;
v_s_3799_ = v_s_3824_;
goto v___jp_3797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3832_, lean_object* v_prio_3833_){
_start:
{
lean_object* v_pos_3834_; lean_object* v_errorMsg_3835_; lean_object* v___y_3837_; 
v_pos_3834_ = lean_ctor_get(v_s_3832_, 2);
v_errorMsg_3835_ = lean_ctor_get(v_s_3832_, 4);
if (lean_obj_tag(v_errorMsg_3835_) == 0)
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_unsigned_to_nat(1u);
v___y_3837_ = v___x_3840_;
goto v___jp_3836_;
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_unsigned_to_nat(0u);
v___y_3837_ = v___x_3841_;
goto v___jp_3836_;
}
v___jp_3836_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___y_3837_);
lean_ctor_set(v___x_3838_, 1, v_prio_3833_);
lean_inc(v_pos_3834_);
v___x_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3839_, 0, v_pos_3834_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
return v___x_3839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3842_, lean_object* v_prio_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3842_, v_prio_3843_);
lean_dec_ref(v_s_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3845_, lean_object* v_startSize_3846_, lean_object* v_startLhsPrec_3847_, lean_object* v_startPos_3848_, lean_object* v_prevPrio_3849_, lean_object* v_prio_3850_, lean_object* v_p_3851_, lean_object* v_c_3852_, lean_object* v_s_3853_){
_start:
{
lean_object* v_lhsPrec_3854_; lean_object* v_pos_3855_; lean_object* v_errorMsg_3856_; lean_object* v_previousScore_3857_; lean_object* v_fst_3858_; lean_object* v_snd_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3915_; 
v_lhsPrec_3854_ = lean_ctor_get(v_s_3853_, 1);
lean_inc(v_lhsPrec_3854_);
v_pos_3855_ = lean_ctor_get(v_s_3853_, 2);
lean_inc(v_pos_3855_);
v_errorMsg_3856_ = lean_ctor_get(v_s_3853_, 4);
lean_inc(v_errorMsg_3856_);
lean_inc(v_prevPrio_3849_);
v_previousScore_3857_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3853_, v_prevPrio_3849_);
v_fst_3858_ = lean_ctor_get(v_previousScore_3857_, 0);
v_snd_3859_ = lean_ctor_get(v_previousScore_3857_, 1);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_previousScore_3857_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3861_ = v_previousScore_3857_;
v_isShared_3862_ = v_isSharedCheck_3915_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_snd_3859_);
lean_inc(v_fst_3858_);
lean_dec(v_previousScore_3857_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3915_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_prevSize_3863_; lean_object* v_s_3864_; lean_object* v_s_3865_; lean_object* v___x_3874_; lean_object* v_fst_3875_; lean_object* v_snd_3876_; uint8_t v___x_3877_; 
v_prevSize_3863_ = l_Lean_Parser_ParserState_stackSize(v_s_3853_);
v_s_3864_ = l_Lean_Parser_ParserState_restore(v_s_3853_, v_prevSize_3863_, v_startPos_3848_);
v_s_3865_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3845_, v_startLhsPrec_3847_, v_p_3851_, v_c_3852_, v_s_3864_);
lean_inc(v_prio_3850_);
v___x_3874_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3865_, v_prio_3850_);
v_fst_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_fst_3875_);
v_snd_3876_ = lean_ctor_get(v___x_3874_, 1);
lean_inc(v_snd_3876_);
lean_dec_ref(v___x_3874_);
v___x_3877_ = lean_nat_dec_lt(v_fst_3858_, v_fst_3875_);
if (v___x_3877_ == 0)
{
uint8_t v___x_3878_; 
v___x_3878_ = lean_nat_dec_eq(v_fst_3858_, v_fst_3875_);
lean_dec(v_fst_3875_);
lean_dec(v_fst_3858_);
if (v___x_3878_ == 0)
{
lean_dec(v_snd_3876_);
lean_del_object(v___x_3861_);
lean_dec(v_snd_3859_);
lean_dec(v_prio_3850_);
goto v___jp_3871_;
}
else
{
lean_object* v_fst_3879_; lean_object* v_snd_3880_; lean_object* v_fst_3881_; lean_object* v_snd_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3914_; 
v_fst_3879_ = lean_ctor_get(v_snd_3859_, 0);
lean_inc(v_fst_3879_);
v_snd_3880_ = lean_ctor_get(v_snd_3859_, 1);
lean_inc(v_snd_3880_);
lean_dec(v_snd_3859_);
v_fst_3881_ = lean_ctor_get(v_snd_3876_, 0);
v_snd_3882_ = lean_ctor_get(v_snd_3876_, 1);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_snd_3876_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3884_ = v_snd_3876_;
v_isShared_3885_ = v_isSharedCheck_3914_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_snd_3882_);
lean_inc(v_fst_3881_);
lean_dec(v_snd_3876_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3914_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
uint8_t v___x_3886_; 
v___x_3886_ = lean_nat_dec_lt(v_fst_3879_, v_fst_3881_);
if (v___x_3886_ == 0)
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_nat_dec_eq(v_fst_3879_, v_fst_3881_);
lean_dec(v_fst_3881_);
lean_dec(v_fst_3879_);
if (v___x_3887_ == 0)
{
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_snd_3880_);
lean_del_object(v___x_3861_);
lean_dec(v_prio_3850_);
goto v___jp_3871_;
}
else
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_nat_dec_lt(v_snd_3880_, v_snd_3882_);
if (v___x_3888_ == 0)
{
uint8_t v___x_3889_; 
lean_del_object(v___x_3861_);
v___x_3889_ = lean_nat_dec_eq(v_snd_3880_, v_snd_3882_);
lean_dec(v_snd_3882_);
lean_dec(v_snd_3880_);
if (v___x_3889_ == 0)
{
lean_del_object(v___x_3884_);
lean_dec(v_prio_3850_);
goto v___jp_3871_;
}
else
{
lean_dec(v_pos_3855_);
lean_dec(v_prevPrio_3849_);
if (lean_obj_tag(v_errorMsg_3856_) == 0)
{
lean_object* v_stxStack_3890_; lean_object* v_lhsPrec_3891_; lean_object* v_pos_3892_; lean_object* v_cache_3893_; lean_object* v_errorMsg_3894_; lean_object* v_recoveredErrors_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v_prevSize_3863_);
v_stxStack_3890_ = lean_ctor_get(v_s_3865_, 0);
v_lhsPrec_3891_ = lean_ctor_get(v_s_3865_, 1);
v_pos_3892_ = lean_ctor_get(v_s_3865_, 2);
v_cache_3893_ = lean_ctor_get(v_s_3865_, 3);
v_errorMsg_3894_ = lean_ctor_get(v_s_3865_, 4);
v_recoveredErrors_3895_ = lean_ctor_get(v_s_3865_, 5);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_s_3865_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3897_ = v_s_3865_;
v_isShared_3898_ = v_isSharedCheck_3908_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_recoveredErrors_3895_);
lean_inc(v_errorMsg_3894_);
lean_inc(v_cache_3893_);
lean_inc(v_pos_3892_);
lean_inc(v_lhsPrec_3891_);
lean_inc(v_stxStack_3890_);
lean_dec(v_s_3865_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3908_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___y_3900_; uint8_t v___x_3907_; 
v___x_3907_ = lean_nat_dec_le(v_lhsPrec_3891_, v_lhsPrec_3854_);
if (v___x_3907_ == 0)
{
lean_dec(v_lhsPrec_3891_);
v___y_3900_ = v_lhsPrec_3854_;
goto v___jp_3899_;
}
else
{
lean_dec(v_lhsPrec_3854_);
v___y_3900_ = v_lhsPrec_3891_;
goto v___jp_3899_;
}
v___jp_3899_:
{
lean_object* v___x_3902_; 
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 1, v___y_3900_);
v___x_3902_ = v___x_3897_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_stxStack_3890_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v___y_3900_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_pos_3892_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_cache_3893_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v_errorMsg_3894_);
lean_ctor_set(v_reuseFailAlloc_3906_, 5, v_recoveredErrors_3895_);
v___x_3902_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 1, v_prio_3850_);
lean_ctor_set(v___x_3884_, 0, v___x_3902_);
v___x_3904_ = v___x_3884_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_prio_3850_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
else
{
lean_object* v_val_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
lean_dec(v_lhsPrec_3854_);
v_val_3909_ = lean_ctor_get(v_errorMsg_3856_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v_errorMsg_3856_, 1);
v___x_3910_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3865_, v_prevSize_3863_, v_val_3909_);
lean_dec(v_prevSize_3863_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 1, v_prio_3850_);
lean_ctor_set(v___x_3884_, 0, v___x_3910_);
v___x_3912_ = v___x_3884_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_prio_3850_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_prevSize_3863_);
lean_dec(v_errorMsg_3856_);
lean_dec(v_pos_3855_);
lean_dec(v_lhsPrec_3854_);
lean_dec(v_prevPrio_3849_);
goto v___jp_3866_;
}
}
}
else
{
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_fst_3881_);
lean_dec(v_snd_3880_);
lean_dec(v_fst_3879_);
lean_dec(v_prevSize_3863_);
lean_dec(v_errorMsg_3856_);
lean_dec(v_pos_3855_);
lean_dec(v_lhsPrec_3854_);
lean_dec(v_prevPrio_3849_);
goto v___jp_3866_;
}
}
}
}
else
{
lean_dec(v_snd_3876_);
lean_dec(v_fst_3875_);
lean_dec(v_prevSize_3863_);
lean_dec(v_snd_3859_);
lean_dec(v_fst_3858_);
lean_dec(v_errorMsg_3856_);
lean_dec(v_pos_3855_);
lean_dec(v_lhsPrec_3854_);
lean_dec(v_prevPrio_3849_);
goto v___jp_3866_;
}
v___jp_3866_:
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = l_Lean_Parser_ParserState_keepNewError(v_s_3865_, v_startSize_3846_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v_prio_3850_);
lean_ctor_set(v___x_3861_, 0, v___x_3867_);
v___x_3869_ = v___x_3861_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_prio_3850_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
v___jp_3871_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3865_, v_prevSize_3863_, v_pos_3855_, v_errorMsg_3856_, v_lhsPrec_3854_);
lean_dec(v_prevSize_3863_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
lean_ctor_set(v___x_3873_, 1, v_prevPrio_3849_);
return v___x_3873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3916_, lean_object* v_startSize_3917_, lean_object* v_startLhsPrec_3918_, lean_object* v_startPos_3919_, lean_object* v_prevPrio_3920_, lean_object* v_prio_3921_, lean_object* v_p_3922_, lean_object* v_c_3923_, lean_object* v_s_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3916_, v_startSize_3917_, v_startLhsPrec_3918_, v_startPos_3919_, v_prevPrio_3920_, v_prio_3921_, v_p_3922_, v_c_3923_, v_s_3924_);
lean_dec(v_startSize_3917_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3926_, lean_object* v_s_3927_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_startSize_3926_, v___x_3928_);
v___x_3930_ = l_Lean_Parser_ParserState_stackSize(v_s_3927_);
v___x_3931_ = lean_nat_dec_lt(v___x_3929_, v___x_3930_);
lean_dec(v___x_3930_);
lean_dec(v___x_3929_);
if (v___x_3931_ == 0)
{
return v_s_3927_;
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3933_ = l_Lean_Parser_ParserState_mkNode(v_s_3927_, v___x_3932_, v_startSize_3926_);
return v___x_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3934_, lean_object* v_s_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3934_, v_s_3935_);
lean_dec(v_startSize_3934_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3937_, lean_object* v_startSize_3938_, lean_object* v_startLhsPrec_3939_, lean_object* v_startPos_3940_, lean_object* v_prevPrio_3941_, lean_object* v_ps_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
if (lean_obj_tag(v_ps_3942_) == 0)
{
lean_object* v___x_3945_; 
lean_dec_ref(v_a_3943_);
lean_dec(v_prevPrio_3941_);
lean_dec(v_startPos_3940_);
lean_dec(v_startLhsPrec_3939_);
lean_dec(v_left_x3f_3937_);
v___x_3945_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3938_, v_a_3944_);
return v___x_3945_;
}
else
{
lean_object* v_head_3946_; lean_object* v_fst_3947_; lean_object* v_tail_3948_; lean_object* v_snd_3949_; lean_object* v_fn_3950_; lean_object* v___x_3951_; lean_object* v_fst_3952_; lean_object* v_snd_3953_; 
v_head_3946_ = lean_ctor_get(v_ps_3942_, 0);
lean_inc(v_head_3946_);
v_fst_3947_ = lean_ctor_get(v_head_3946_, 0);
lean_inc(v_fst_3947_);
v_tail_3948_ = lean_ctor_get(v_ps_3942_, 1);
lean_inc(v_tail_3948_);
lean_dec_ref_known(v_ps_3942_, 2);
v_snd_3949_ = lean_ctor_get(v_head_3946_, 1);
lean_inc(v_snd_3949_);
lean_dec(v_head_3946_);
v_fn_3950_ = lean_ctor_get(v_fst_3947_, 1);
lean_inc_ref(v_fn_3950_);
lean_dec(v_fst_3947_);
lean_inc_ref(v_a_3943_);
lean_inc(v_startPos_3940_);
lean_inc(v_startLhsPrec_3939_);
lean_inc(v_left_x3f_3937_);
v___x_3951_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3937_, v_startSize_3938_, v_startLhsPrec_3939_, v_startPos_3940_, v_prevPrio_3941_, v_snd_3949_, v_fn_3950_, v_a_3943_, v_a_3944_);
v_fst_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_fst_3952_);
v_snd_3953_ = lean_ctor_get(v___x_3951_, 1);
lean_inc(v_snd_3953_);
lean_dec_ref(v___x_3951_);
v_prevPrio_3941_ = v_snd_3953_;
v_ps_3942_ = v_tail_3948_;
v_a_3944_ = v_fst_3952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3955_, lean_object* v_startSize_3956_, lean_object* v_startLhsPrec_3957_, lean_object* v_startPos_3958_, lean_object* v_prevPrio_3959_, lean_object* v_ps_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3955_, v_startSize_3956_, v_startLhsPrec_3957_, v_startPos_3958_, v_prevPrio_3959_, v_ps_3960_, v_a_3961_, v_a_3962_);
lean_dec(v_startSize_3956_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3964_, lean_object* v_startSize_3965_, lean_object* v_startLhsPrec_3966_, lean_object* v_startPos_3967_, lean_object* v_prevPrio_3968_, lean_object* v_ps_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3964_, v_startSize_3965_, v_startLhsPrec_3966_, v_startPos_3967_, v_prevPrio_3968_, v_ps_3969_, v_a_3970_, v_a_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3973_, lean_object* v_startSize_3974_, lean_object* v_startLhsPrec_3975_, lean_object* v_startPos_3976_, lean_object* v_prevPrio_3977_, lean_object* v_ps_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3973_, v_startSize_3974_, v_startLhsPrec_3975_, v_startPos_3976_, v_prevPrio_3977_, v_ps_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_startSize_3974_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3983_, lean_object* v_x_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_dec_ref(v_a_3985_);
lean_dec(v_left_x3f_3983_);
v___x_3987_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3988_ = l_Lean_Parser_ParserState_mkError(v_a_3986_, v___x_3987_);
return v___x_3988_;
}
else
{
lean_object* v_tail_3989_; 
v_tail_3989_ = lean_ctor_get(v_x_3984_, 1);
if (lean_obj_tag(v_tail_3989_) == 0)
{
lean_object* v_head_3990_; lean_object* v_fst_3991_; lean_object* v_lhsPrec_3992_; lean_object* v_fn_3993_; lean_object* v___x_3994_; 
v_head_3990_ = lean_ctor_get(v_x_3984_, 0);
lean_inc(v_head_3990_);
lean_dec_ref_known(v_x_3984_, 2);
v_fst_3991_ = lean_ctor_get(v_head_3990_, 0);
lean_inc(v_fst_3991_);
lean_dec(v_head_3990_);
v_lhsPrec_3992_ = lean_ctor_get(v_a_3986_, 1);
lean_inc(v_lhsPrec_3992_);
v_fn_3993_ = lean_ctor_get(v_fst_3991_, 1);
lean_inc_ref(v_fn_3993_);
lean_dec(v_fst_3991_);
v___x_3994_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3983_, v_lhsPrec_3992_, v_fn_3993_, v_a_3985_, v_a_3986_);
return v___x_3994_;
}
else
{
lean_object* v_head_3995_; lean_object* v_fst_3996_; lean_object* v_lhsPrec_3997_; lean_object* v_pos_3998_; lean_object* v_snd_3999_; lean_object* v_fn_4000_; lean_object* v_startSize_4001_; lean_object* v_s_4002_; lean_object* v___x_4003_; 
lean_inc(v_tail_3989_);
v_head_3995_ = lean_ctor_get(v_x_3984_, 0);
lean_inc(v_head_3995_);
lean_dec_ref_known(v_x_3984_, 2);
v_fst_3996_ = lean_ctor_get(v_head_3995_, 0);
lean_inc(v_fst_3996_);
v_lhsPrec_3997_ = lean_ctor_get(v_a_3986_, 1);
lean_inc_n(v_lhsPrec_3997_, 2);
v_pos_3998_ = lean_ctor_get(v_a_3986_, 2);
lean_inc(v_pos_3998_);
v_snd_3999_ = lean_ctor_get(v_head_3995_, 1);
lean_inc(v_snd_3999_);
lean_dec(v_head_3995_);
v_fn_4000_ = lean_ctor_get(v_fst_3996_, 1);
lean_inc_ref(v_fn_4000_);
lean_dec(v_fst_3996_);
v_startSize_4001_ = l_Lean_Parser_ParserState_stackSize(v_a_3986_);
lean_inc_ref(v_a_3985_);
lean_inc(v_left_x3f_3983_);
v_s_4002_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3983_, v_lhsPrec_3997_, v_fn_4000_, v_a_3985_, v_a_3986_);
v___x_4003_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3983_, v_startSize_4001_, v_lhsPrec_3997_, v_pos_3998_, v_snd_3999_, v_tail_3989_, v_a_3985_, v_s_4002_);
lean_dec(v_startSize_4001_);
return v___x_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_4005_, lean_object* v_x_4006_, lean_object* v_x_4007_){
_start:
{
if (lean_obj_tag(v_x_4005_) == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec_ref(v_x_4006_);
v___x_4008_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_4009_ = l_Lean_Parser_ParserState_mkError(v_x_4007_, v___x_4008_);
return v___x_4009_;
}
else
{
lean_object* v_tail_4010_; 
v_tail_4010_ = lean_ctor_get(v_x_4005_, 1);
if (lean_obj_tag(v_tail_4010_) == 0)
{
lean_object* v_head_4011_; lean_object* v_fn_4012_; lean_object* v___x_4013_; 
v_head_4011_ = lean_ctor_get(v_x_4005_, 0);
lean_inc(v_head_4011_);
lean_dec_ref_known(v_x_4005_, 2);
v_fn_4012_ = lean_ctor_get(v_head_4011_, 1);
lean_inc_ref(v_fn_4012_);
lean_dec(v_head_4011_);
v___x_4013_ = lean_apply_2(v_fn_4012_, v_x_4006_, v_x_4007_);
return v___x_4013_;
}
else
{
lean_object* v_head_4014_; lean_object* v_fn_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_inc(v_tail_4010_);
v_head_4014_ = lean_ctor_get(v_x_4005_, 0);
lean_inc(v_head_4014_);
lean_dec_ref_known(v_x_4005_, 2);
v_fn_4015_ = lean_ctor_get(v_head_4014_, 1);
lean_inc_ref(v_fn_4015_);
lean_dec(v_head_4014_);
v___x_4016_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_4016_, 0, v_tail_4010_);
v___x_4017_ = l_Lean_Parser_orelseFn(v_fn_4015_, v___x_4016_, v_x_4006_, v_x_4007_);
return v___x_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_4018_, lean_object* v_c_4019_, lean_object* v_s_4020_){
_start:
{
lean_object* v_toCacheableParserContext_4021_; lean_object* v_savedPos_x3f_4022_; 
v_toCacheableParserContext_4021_ = lean_ctor_get(v_c_4019_, 2);
v_savedPos_x3f_4022_ = lean_ctor_get(v_toCacheableParserContext_4021_, 2);
lean_inc(v_savedPos_x3f_4022_);
if (lean_obj_tag(v_savedPos_x3f_4022_) == 0)
{
lean_dec_ref(v_c_4019_);
lean_dec_ref(v_errorMsg_4018_);
return v_s_4020_;
}
else
{
lean_object* v_toInputContext_4023_; lean_object* v_val_4024_; lean_object* v_fileMap_4025_; lean_object* v_pos_4026_; lean_object* v_savedPos_4027_; lean_object* v_pos_4028_; lean_object* v_column_4029_; lean_object* v_column_4030_; uint8_t v___x_4031_; 
v_toInputContext_4023_ = lean_ctor_get(v_c_4019_, 0);
lean_inc_ref(v_toInputContext_4023_);
lean_dec_ref(v_c_4019_);
v_val_4024_ = lean_ctor_get(v_savedPos_x3f_4022_, 0);
lean_inc(v_val_4024_);
lean_dec_ref_known(v_savedPos_x3f_4022_, 1);
v_fileMap_4025_ = lean_ctor_get(v_toInputContext_4023_, 2);
lean_inc_ref_n(v_fileMap_4025_, 2);
lean_dec_ref(v_toInputContext_4023_);
v_pos_4026_ = lean_ctor_get(v_s_4020_, 2);
v_savedPos_4027_ = l_Lean_FileMap_toPosition(v_fileMap_4025_, v_val_4024_);
lean_dec(v_val_4024_);
v_pos_4028_ = l_Lean_FileMap_toPosition(v_fileMap_4025_, v_pos_4026_);
v_column_4029_ = lean_ctor_get(v_pos_4028_, 1);
lean_inc(v_column_4029_);
lean_dec_ref(v_pos_4028_);
v_column_4030_ = lean_ctor_get(v_savedPos_4027_, 1);
lean_inc(v_column_4030_);
lean_dec_ref(v_savedPos_4027_);
v___x_4031_ = lean_nat_dec_eq(v_column_4029_, v_column_4030_);
lean_dec(v_column_4030_);
lean_dec(v_column_4029_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_Parser_ParserState_mkError(v_s_4020_, v_errorMsg_4018_);
return v___x_4032_;
}
else
{
lean_dec_ref(v_errorMsg_4018_);
return v_s_4020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4035_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_4035_, 0, v_errorMsg_4033_);
v___x_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4045_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4046_ = l_Lean_addBuiltinDocString(v___x_4044_, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4049_, lean_object* v_c_4050_, lean_object* v_s_4051_){
_start:
{
lean_object* v_toCacheableParserContext_4052_; lean_object* v_savedPos_x3f_4053_; 
v_toCacheableParserContext_4052_ = lean_ctor_get(v_c_4050_, 2);
v_savedPos_x3f_4053_ = lean_ctor_get(v_toCacheableParserContext_4052_, 2);
lean_inc(v_savedPos_x3f_4053_);
if (lean_obj_tag(v_savedPos_x3f_4053_) == 0)
{
lean_dec_ref(v_c_4050_);
lean_dec_ref(v_errorMsg_4049_);
return v_s_4051_;
}
else
{
lean_object* v_toInputContext_4054_; lean_object* v_val_4055_; lean_object* v_fileMap_4056_; lean_object* v_pos_4057_; lean_object* v_savedPos_4058_; lean_object* v_column_4059_; lean_object* v_pos_4060_; lean_object* v_column_4061_; uint8_t v___x_4062_; 
v_toInputContext_4054_ = lean_ctor_get(v_c_4050_, 0);
lean_inc_ref(v_toInputContext_4054_);
lean_dec_ref(v_c_4050_);
v_val_4055_ = lean_ctor_get(v_savedPos_x3f_4053_, 0);
lean_inc(v_val_4055_);
lean_dec_ref_known(v_savedPos_x3f_4053_, 1);
v_fileMap_4056_ = lean_ctor_get(v_toInputContext_4054_, 2);
lean_inc_ref_n(v_fileMap_4056_, 2);
lean_dec_ref(v_toInputContext_4054_);
v_pos_4057_ = lean_ctor_get(v_s_4051_, 2);
v_savedPos_4058_ = l_Lean_FileMap_toPosition(v_fileMap_4056_, v_val_4055_);
lean_dec(v_val_4055_);
v_column_4059_ = lean_ctor_get(v_savedPos_4058_, 1);
lean_inc(v_column_4059_);
lean_dec_ref(v_savedPos_4058_);
v_pos_4060_ = l_Lean_FileMap_toPosition(v_fileMap_4056_, v_pos_4057_);
v_column_4061_ = lean_ctor_get(v_pos_4060_, 1);
lean_inc(v_column_4061_);
lean_dec_ref(v_pos_4060_);
v___x_4062_ = lean_nat_dec_le(v_column_4059_, v_column_4061_);
lean_dec(v_column_4061_);
lean_dec(v_column_4059_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Parser_ParserState_mkError(v_s_4051_, v_errorMsg_4049_);
return v___x_4063_;
}
else
{
lean_dec_ref(v_errorMsg_4049_);
return v_s_4051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4064_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4066_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4066_, 0, v_errorMsg_4064_);
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4065_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4076_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4077_ = l_Lean_addBuiltinDocString(v___x_4075_, v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4080_, lean_object* v_c_4081_, lean_object* v_s_4082_){
_start:
{
lean_object* v_toCacheableParserContext_4083_; lean_object* v_savedPos_x3f_4084_; 
v_toCacheableParserContext_4083_ = lean_ctor_get(v_c_4081_, 2);
v_savedPos_x3f_4084_ = lean_ctor_get(v_toCacheableParserContext_4083_, 2);
lean_inc(v_savedPos_x3f_4084_);
if (lean_obj_tag(v_savedPos_x3f_4084_) == 0)
{
lean_dec_ref(v_c_4081_);
lean_dec_ref(v_errorMsg_4080_);
return v_s_4082_;
}
else
{
lean_object* v_toInputContext_4085_; lean_object* v_val_4086_; lean_object* v_fileMap_4087_; lean_object* v_pos_4088_; lean_object* v_savedPos_4089_; lean_object* v_column_4090_; lean_object* v_pos_4091_; lean_object* v_column_4092_; uint8_t v___x_4093_; 
v_toInputContext_4085_ = lean_ctor_get(v_c_4081_, 0);
lean_inc_ref(v_toInputContext_4085_);
lean_dec_ref(v_c_4081_);
v_val_4086_ = lean_ctor_get(v_savedPos_x3f_4084_, 0);
lean_inc(v_val_4086_);
lean_dec_ref_known(v_savedPos_x3f_4084_, 1);
v_fileMap_4087_ = lean_ctor_get(v_toInputContext_4085_, 2);
lean_inc_ref_n(v_fileMap_4087_, 2);
lean_dec_ref(v_toInputContext_4085_);
v_pos_4088_ = lean_ctor_get(v_s_4082_, 2);
v_savedPos_4089_ = l_Lean_FileMap_toPosition(v_fileMap_4087_, v_val_4086_);
lean_dec(v_val_4086_);
v_column_4090_ = lean_ctor_get(v_savedPos_4089_, 1);
lean_inc(v_column_4090_);
lean_dec_ref(v_savedPos_4089_);
v_pos_4091_ = l_Lean_FileMap_toPosition(v_fileMap_4087_, v_pos_4088_);
v_column_4092_ = lean_ctor_get(v_pos_4091_, 1);
lean_inc(v_column_4092_);
lean_dec_ref(v_pos_4091_);
v___x_4093_ = lean_nat_dec_lt(v_column_4090_, v_column_4092_);
lean_dec(v_column_4092_);
lean_dec(v_column_4090_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_Parser_ParserState_mkError(v_s_4082_, v_errorMsg_4080_);
return v___x_4094_;
}
else
{
lean_dec_ref(v_errorMsg_4080_);
return v_s_4082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4097_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4097_, 0, v_errorMsg_4095_);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4107_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4108_ = l_Lean_addBuiltinDocString(v___x_4106_, v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4111_, lean_object* v_c_4112_, lean_object* v_s_4113_){
_start:
{
lean_object* v_toCacheableParserContext_4114_; lean_object* v_savedPos_x3f_4115_; 
v_toCacheableParserContext_4114_ = lean_ctor_get(v_c_4112_, 2);
v_savedPos_x3f_4115_ = lean_ctor_get(v_toCacheableParserContext_4114_, 2);
lean_inc(v_savedPos_x3f_4115_);
if (lean_obj_tag(v_savedPos_x3f_4115_) == 0)
{
lean_dec_ref(v_c_4112_);
lean_dec_ref(v_errorMsg_4111_);
return v_s_4113_;
}
else
{
lean_object* v_toInputContext_4116_; lean_object* v_val_4117_; lean_object* v_fileMap_4118_; lean_object* v_pos_4119_; lean_object* v_savedPos_4120_; lean_object* v_pos_4121_; lean_object* v_line_4122_; lean_object* v_line_4123_; uint8_t v___x_4124_; 
v_toInputContext_4116_ = lean_ctor_get(v_c_4112_, 0);
lean_inc_ref(v_toInputContext_4116_);
lean_dec_ref(v_c_4112_);
v_val_4117_ = lean_ctor_get(v_savedPos_x3f_4115_, 0);
lean_inc(v_val_4117_);
lean_dec_ref_known(v_savedPos_x3f_4115_, 1);
v_fileMap_4118_ = lean_ctor_get(v_toInputContext_4116_, 2);
lean_inc_ref_n(v_fileMap_4118_, 2);
lean_dec_ref(v_toInputContext_4116_);
v_pos_4119_ = lean_ctor_get(v_s_4113_, 2);
v_savedPos_4120_ = l_Lean_FileMap_toPosition(v_fileMap_4118_, v_val_4117_);
lean_dec(v_val_4117_);
v_pos_4121_ = l_Lean_FileMap_toPosition(v_fileMap_4118_, v_pos_4119_);
v_line_4122_ = lean_ctor_get(v_pos_4121_, 0);
lean_inc(v_line_4122_);
lean_dec_ref(v_pos_4121_);
v_line_4123_ = lean_ctor_get(v_savedPos_4120_, 0);
lean_inc(v_line_4123_);
lean_dec_ref(v_savedPos_4120_);
v___x_4124_ = lean_nat_dec_eq(v_line_4122_, v_line_4123_);
lean_dec(v_line_4123_);
lean_dec(v_line_4122_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Parser_ParserState_mkError(v_s_4113_, v_errorMsg_4111_);
return v___x_4125_;
}
else
{
lean_dec_ref(v_errorMsg_4111_);
return v_s_4113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4126_){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4128_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4128_, 0, v_errorMsg_4126_);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4137_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4138_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4139_ = l_Lean_addBuiltinDocString(v___x_4137_, v___x_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4142_, lean_object* v_x_4143_){
_start:
{
lean_object* v_prec_4144_; lean_object* v_quotDepth_4145_; uint8_t v_suppressInsideQuot_4146_; lean_object* v_forbiddenTk_x3f_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4156_; 
v_prec_4144_ = lean_ctor_get(v_x_4143_, 0);
v_quotDepth_4145_ = lean_ctor_get(v_x_4143_, 1);
v_suppressInsideQuot_4146_ = lean_ctor_get_uint8(v_x_4143_, sizeof(void*)*4);
v_forbiddenTk_x3f_4147_ = lean_ctor_get(v_x_4143_, 3);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_x_4143_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v_x_4143_, 2);
lean_dec(v_unused_4157_);
v___x_4149_ = v_x_4143_;
v_isShared_4150_ = v_isSharedCheck_4156_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4147_);
lean_inc(v_quotDepth_4145_);
lean_inc(v_prec_4144_);
lean_dec(v_x_4143_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4156_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v_pos_4151_; lean_object* v___x_4152_; lean_object* v___x_4154_; 
v_pos_4151_ = lean_ctor_get(v___y_4142_, 2);
lean_inc(v_pos_4151_);
v___x_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4152_, 0, v_pos_4151_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 2, v___x_4152_);
v___x_4154_ = v___x_4149_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_prec_4144_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_quotDepth_4145_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4155_, 3, v_forbiddenTk_x3f_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4155_, sizeof(void*)*4, v_suppressInsideQuot_4146_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Parser_withPosition___lam__0(v___y_4158_, v_x_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___f_4164_; lean_object* v___x_4165_; 
lean_inc_ref(v___y_4163_);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4164_, 0, v___y_4163_);
v___x_4165_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4164_, v_fn_4161_, v___y_4162_, v___y_4163_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4166_){
_start:
{
lean_object* v_info_4167_; lean_object* v_fn_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4176_; 
v_info_4167_ = lean_ctor_get(v_p_4166_, 0);
v_fn_4168_ = lean_ctor_get(v_p_4166_, 1);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_p_4166_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4170_ = v_p_4166_;
v_isShared_4171_ = v_isSharedCheck_4176_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_fn_4168_);
lean_inc(v_info_4167_);
lean_dec(v_p_4166_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4176_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___f_4172_; lean_object* v___x_4174_; 
v___f_4172_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4172_, 0, v_fn_4168_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 1, v___f_4172_);
v___x_4174_ = v___x_4170_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_info_4167_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___f_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4185_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4186_ = l_Lean_addBuiltinDocString(v___x_4184_, v___x_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4189_, lean_object* v_pos_4190_, lean_object* v_c_4191_){
_start:
{
uint8_t v___x_4192_; 
v___x_4192_ = l_Lean_Parser_checkTailLinebreak(v_prev_4189_);
if (v___x_4192_ == 0)
{
lean_dec(v_pos_4190_);
return v_c_4191_;
}
else
{
lean_object* v_prec_4193_; lean_object* v_quotDepth_4194_; uint8_t v_suppressInsideQuot_4195_; lean_object* v_forbiddenTk_x3f_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4204_; 
v_prec_4193_ = lean_ctor_get(v_c_4191_, 0);
v_quotDepth_4194_ = lean_ctor_get(v_c_4191_, 1);
v_suppressInsideQuot_4195_ = lean_ctor_get_uint8(v_c_4191_, sizeof(void*)*4);
v_forbiddenTk_x3f_4196_ = lean_ctor_get(v_c_4191_, 3);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_c_4191_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; 
v_unused_4205_ = lean_ctor_get(v_c_4191_, 2);
lean_dec(v_unused_4205_);
v___x_4198_ = v_c_4191_;
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4196_);
lean_inc(v_quotDepth_4194_);
lean_inc(v_prec_4193_);
lean_dec(v_c_4191_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4200_, 0, v_pos_4190_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 2, v___x_4200_);
v___x_4202_ = v___x_4198_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_prec_4193_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v_quotDepth_4194_);
lean_ctor_set(v_reuseFailAlloc_4203_, 2, v___x_4200_);
lean_ctor_set(v_reuseFailAlloc_4203_, 3, v_forbiddenTk_x3f_4196_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, sizeof(void*)*4, v_suppressInsideQuot_4195_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4206_, lean_object* v_pos_4207_, lean_object* v_c_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4206_, v_pos_4207_, v_c_4208_);
lean_dec(v_prev_4206_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_stxStack_4213_; lean_object* v_pos_4214_; lean_object* v_prev_4215_; lean_object* v___f_4216_; lean_object* v___x_4217_; 
v_stxStack_4213_ = lean_ctor_get(v___y_4212_, 0);
v_pos_4214_ = lean_ctor_get(v___y_4212_, 2);
v_prev_4215_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4213_);
lean_inc(v_pos_4214_);
v___f_4216_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4216_, 0, v_prev_4215_);
lean_closure_set(v___f_4216_, 1, v_pos_4214_);
v___x_4217_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4216_, v_fn_4210_, v___y_4211_, v___y_4212_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4218_){
_start:
{
lean_object* v_info_4219_; lean_object* v_fn_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4228_; 
v_info_4219_ = lean_ctor_get(v_p_4218_, 0);
v_fn_4220_ = lean_ctor_get(v_p_4218_, 1);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_p_4218_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4222_ = v_p_4218_;
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_fn_4220_);
lean_inc(v_info_4219_);
lean_dec(v_p_4218_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___f_4224_; lean_object* v___x_4226_; 
v___f_4224_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4224_, 0, v_fn_4220_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 1, v___f_4224_);
v___x_4226_ = v___x_4222_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_info_4219_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v___f_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4229_){
_start:
{
lean_object* v_prec_4230_; lean_object* v_quotDepth_4231_; uint8_t v_suppressInsideQuot_4232_; lean_object* v_forbiddenTk_x3f_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4241_; 
v_prec_4230_ = lean_ctor_get(v_x_4229_, 0);
v_quotDepth_4231_ = lean_ctor_get(v_x_4229_, 1);
v_suppressInsideQuot_4232_ = lean_ctor_get_uint8(v_x_4229_, sizeof(void*)*4);
v_forbiddenTk_x3f_4233_ = lean_ctor_get(v_x_4229_, 3);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_x_4229_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; 
v_unused_4242_ = lean_ctor_get(v_x_4229_, 2);
lean_dec(v_unused_4242_);
v___x_4235_ = v_x_4229_;
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4233_);
lean_inc(v_quotDepth_4231_);
lean_inc(v_prec_4230_);
lean_dec(v_x_4229_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4237_ = lean_box(0);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 2, v___x_4237_);
v___x_4239_ = v___x_4235_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_prec_4230_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_quotDepth_4231_);
lean_ctor_set(v_reuseFailAlloc_4240_, 2, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4240_, 3, v_forbiddenTk_x3f_4233_);
lean_ctor_set_uint8(v_reuseFailAlloc_4240_, sizeof(void*)*4, v_suppressInsideQuot_4232_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4244_){
_start:
{
lean_object* v___f_4245_; lean_object* v___x_4246_; 
v___f_4245_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4246_ = l_Lean_Parser_adaptCacheableContext(v___f_4245_, v_p_4244_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4255_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4256_ = l_Lean_addBuiltinDocString(v___x_4254_, v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4259_, lean_object* v_x_4260_){
_start:
{
lean_object* v_prec_4261_; lean_object* v_quotDepth_4262_; uint8_t v_suppressInsideQuot_4263_; lean_object* v_savedPos_x3f_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4272_; 
v_prec_4261_ = lean_ctor_get(v_x_4260_, 0);
v_quotDepth_4262_ = lean_ctor_get(v_x_4260_, 1);
v_suppressInsideQuot_4263_ = lean_ctor_get_uint8(v_x_4260_, sizeof(void*)*4);
v_savedPos_x3f_4264_ = lean_ctor_get(v_x_4260_, 2);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_x_4260_);
if (v_isSharedCheck_4272_ == 0)
{
lean_object* v_unused_4273_; 
v_unused_4273_ = lean_ctor_get(v_x_4260_, 3);
lean_dec(v_unused_4273_);
v___x_4266_ = v_x_4260_;
v_isShared_4267_ = v_isSharedCheck_4272_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_savedPos_x3f_4264_);
lean_inc(v_quotDepth_4262_);
lean_inc(v_prec_4261_);
lean_dec(v_x_4260_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4272_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_tk_4259_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 3, v___x_4268_);
v___x_4270_ = v___x_4266_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_prec_4261_);
lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_quotDepth_4262_);
lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_savedPos_x3f_4264_);
lean_ctor_set(v_reuseFailAlloc_4271_, 3, v___x_4268_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*4, v_suppressInsideQuot_4263_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4274_, lean_object* v_p_4275_){
_start:
{
lean_object* v___f_4276_; lean_object* v___x_4277_; 
v___f_4276_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4276_, 0, v_tk_4274_);
v___x_4277_ = l_Lean_Parser_adaptCacheableContext(v___f_4276_, v_p_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4286_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4287_ = l_Lean_addBuiltinDocString(v___x_4285_, v___x_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4290_){
_start:
{
lean_object* v_prec_4291_; lean_object* v_quotDepth_4292_; uint8_t v_suppressInsideQuot_4293_; lean_object* v_savedPos_x3f_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4302_; 
v_prec_4291_ = lean_ctor_get(v_x_4290_, 0);
v_quotDepth_4292_ = lean_ctor_get(v_x_4290_, 1);
v_suppressInsideQuot_4293_ = lean_ctor_get_uint8(v_x_4290_, sizeof(void*)*4);
v_savedPos_x3f_4294_ = lean_ctor_get(v_x_4290_, 2);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_x_4290_);
if (v_isSharedCheck_4302_ == 0)
{
lean_object* v_unused_4303_; 
v_unused_4303_ = lean_ctor_get(v_x_4290_, 3);
lean_dec(v_unused_4303_);
v___x_4296_ = v_x_4290_;
v_isShared_4297_ = v_isSharedCheck_4302_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_savedPos_x3f_4294_);
lean_inc(v_quotDepth_4292_);
lean_inc(v_prec_4291_);
lean_dec(v_x_4290_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4302_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4298_ = lean_box(0);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 3, v___x_4298_);
v___x_4300_ = v___x_4296_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_prec_4291_);
lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_quotDepth_4292_);
lean_ctor_set(v_reuseFailAlloc_4301_, 2, v_savedPos_x3f_4294_);
lean_ctor_set(v_reuseFailAlloc_4301_, 3, v___x_4298_);
lean_ctor_set_uint8(v_reuseFailAlloc_4301_, sizeof(void*)*4, v_suppressInsideQuot_4293_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4305_){
_start:
{
lean_object* v___f_4306_; lean_object* v___x_4307_; 
v___f_4306_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4307_ = l_Lean_Parser_adaptCacheableContext(v___f_4306_, v_p_4305_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4316_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4317_ = l_Lean_addBuiltinDocString(v___x_4315_, v___x_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4321_, lean_object* v_s_4322_){
_start:
{
lean_object* v_pos_4323_; lean_object* v_toInputContext_4324_; uint8_t v___x_4325_; 
v_pos_4323_ = lean_ctor_get(v_s_4322_, 2);
v_toInputContext_4324_ = lean_ctor_get(v_c_4321_, 0);
v___x_4325_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4324_, v_pos_4323_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4327_ = l_Lean_Parser_ParserState_mkError(v_s_4322_, v___x_4326_);
return v___x_4327_;
}
else
{
return v_s_4322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4328_, lean_object* v_s_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_Parser_eoiFn(v_c_4328_, v_s_4329_);
lean_dec_ref(v_c_4328_);
return v_res_4330_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4331_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4332_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
lean_ctor_set(v___x_4333_, 1, v___x_4331_);
return v___x_4333_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4335_, lean_object* v_v_4336_, lean_object* v_t_4337_){
_start:
{
if (lean_obj_tag(v_t_4337_) == 0)
{
lean_object* v_size_4338_; lean_object* v_k_4339_; lean_object* v_v_4340_; lean_object* v_l_4341_; lean_object* v_r_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4622_; 
v_size_4338_ = lean_ctor_get(v_t_4337_, 0);
v_k_4339_ = lean_ctor_get(v_t_4337_, 1);
v_v_4340_ = lean_ctor_get(v_t_4337_, 2);
v_l_4341_ = lean_ctor_get(v_t_4337_, 3);
v_r_4342_ = lean_ctor_get(v_t_4337_, 4);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_t_4337_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4344_ = v_t_4337_;
v_isShared_4345_ = v_isSharedCheck_4622_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_r_4342_);
lean_inc(v_l_4341_);
lean_inc(v_v_4340_);
lean_inc(v_k_4339_);
lean_inc(v_size_4338_);
lean_dec(v_t_4337_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4622_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
uint8_t v___x_4346_; 
v___x_4346_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4335_, v_k_4339_);
switch(v___x_4346_)
{
case 0:
{
lean_object* v_impl_4347_; lean_object* v___x_4348_; 
lean_dec(v_size_4338_);
v_impl_4347_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4335_, v_v_4336_, v_l_4341_);
v___x_4348_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4342_) == 0)
{
lean_object* v_size_4349_; lean_object* v_size_4350_; lean_object* v_k_4351_; lean_object* v_v_4352_; lean_object* v_l_4353_; lean_object* v_r_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v_size_4349_ = lean_ctor_get(v_r_4342_, 0);
v_size_4350_ = lean_ctor_get(v_impl_4347_, 0);
lean_inc(v_size_4350_);
v_k_4351_ = lean_ctor_get(v_impl_4347_, 1);
lean_inc(v_k_4351_);
v_v_4352_ = lean_ctor_get(v_impl_4347_, 2);
lean_inc(v_v_4352_);
v_l_4353_ = lean_ctor_get(v_impl_4347_, 3);
lean_inc(v_l_4353_);
v_r_4354_ = lean_ctor_get(v_impl_4347_, 4);
lean_inc(v_r_4354_);
v___x_4355_ = lean_unsigned_to_nat(3u);
v___x_4356_ = lean_nat_mul(v___x_4355_, v_size_4349_);
v___x_4357_ = lean_nat_dec_lt(v___x_4356_, v_size_4350_);
lean_dec(v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4361_; 
lean_dec(v_r_4354_);
lean_dec(v_l_4353_);
lean_dec(v_v_4352_);
lean_dec(v_k_4351_);
v___x_4358_ = lean_nat_add(v___x_4348_, v_size_4350_);
lean_dec(v_size_4350_);
v___x_4359_ = lean_nat_add(v___x_4358_, v_size_4349_);
lean_dec(v___x_4358_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 3, v_impl_4347_);
lean_ctor_set(v___x_4344_, 0, v___x_4359_);
v___x_4361_ = v___x_4344_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4362_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4362_, 3, v_impl_4347_);
lean_ctor_set(v_reuseFailAlloc_4362_, 4, v_r_4342_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
else
{
lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4428_; 
v_isSharedCheck_4428_ = !lean_is_exclusive(v_impl_4347_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; lean_object* v_unused_4430_; lean_object* v_unused_4431_; lean_object* v_unused_4432_; lean_object* v_unused_4433_; 
v_unused_4429_ = lean_ctor_get(v_impl_4347_, 4);
lean_dec(v_unused_4429_);
v_unused_4430_ = lean_ctor_get(v_impl_4347_, 3);
lean_dec(v_unused_4430_);
v_unused_4431_ = lean_ctor_get(v_impl_4347_, 2);
lean_dec(v_unused_4431_);
v_unused_4432_ = lean_ctor_get(v_impl_4347_, 1);
lean_dec(v_unused_4432_);
v_unused_4433_ = lean_ctor_get(v_impl_4347_, 0);
lean_dec(v_unused_4433_);
v___x_4364_ = v_impl_4347_;
v_isShared_4365_ = v_isSharedCheck_4428_;
goto v_resetjp_4363_;
}
else
{
lean_dec(v_impl_4347_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4428_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_size_4366_; lean_object* v_size_4367_; lean_object* v_k_4368_; lean_object* v_v_4369_; lean_object* v_l_4370_; lean_object* v_r_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v_size_4366_ = lean_ctor_get(v_l_4353_, 0);
v_size_4367_ = lean_ctor_get(v_r_4354_, 0);
v_k_4368_ = lean_ctor_get(v_r_4354_, 1);
v_v_4369_ = lean_ctor_get(v_r_4354_, 2);
v_l_4370_ = lean_ctor_get(v_r_4354_, 3);
v_r_4371_ = lean_ctor_get(v_r_4354_, 4);
v___x_4372_ = lean_unsigned_to_nat(2u);
v___x_4373_ = lean_nat_mul(v___x_4372_, v_size_4366_);
v___x_4374_ = lean_nat_dec_lt(v_size_4367_, v___x_4373_);
lean_dec(v___x_4373_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4403_; 
lean_inc(v_r_4371_);
lean_inc(v_l_4370_);
lean_inc(v_v_4369_);
lean_inc(v_k_4368_);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_r_4354_);
if (v_isSharedCheck_4403_ == 0)
{
lean_object* v_unused_4404_; lean_object* v_unused_4405_; lean_object* v_unused_4406_; lean_object* v_unused_4407_; lean_object* v_unused_4408_; 
v_unused_4404_ = lean_ctor_get(v_r_4354_, 4);
lean_dec(v_unused_4404_);
v_unused_4405_ = lean_ctor_get(v_r_4354_, 3);
lean_dec(v_unused_4405_);
v_unused_4406_ = lean_ctor_get(v_r_4354_, 2);
lean_dec(v_unused_4406_);
v_unused_4407_ = lean_ctor_get(v_r_4354_, 1);
lean_dec(v_unused_4407_);
v_unused_4408_ = lean_ctor_get(v_r_4354_, 0);
lean_dec(v_unused_4408_);
v___x_4376_ = v_r_4354_;
v_isShared_4377_ = v_isSharedCheck_4403_;
goto v_resetjp_4375_;
}
else
{
lean_dec(v_r_4354_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4403_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___x_4391_; lean_object* v___y_4393_; 
v___x_4378_ = lean_nat_add(v___x_4348_, v_size_4350_);
lean_dec(v_size_4350_);
v___x_4379_ = lean_nat_add(v___x_4378_, v_size_4349_);
lean_dec(v___x_4378_);
v___x_4391_ = lean_nat_add(v___x_4348_, v_size_4366_);
if (lean_obj_tag(v_l_4370_) == 0)
{
lean_object* v_size_4401_; 
v_size_4401_ = lean_ctor_get(v_l_4370_, 0);
lean_inc(v_size_4401_);
v___y_4393_ = v_size_4401_;
goto v___jp_4392_;
}
else
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_unsigned_to_nat(0u);
v___y_4393_ = v___x_4402_;
goto v___jp_4392_;
}
v___jp_4380_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = lean_nat_add(v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec(v___y_4382_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 4, v_r_4342_);
lean_ctor_set(v___x_4376_, 3, v_r_4371_);
lean_ctor_set(v___x_4376_, 2, v_v_4340_);
lean_ctor_set(v___x_4376_, 1, v_k_4339_);
lean_ctor_set(v___x_4376_, 0, v___x_4384_);
v___x_4386_ = v___x_4376_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v_r_4371_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v_r_4342_);
v___x_4386_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
lean_object* v___x_4388_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v___x_4386_);
lean_ctor_set(v___x_4364_, 3, v___y_4381_);
lean_ctor_set(v___x_4364_, 2, v_v_4369_);
lean_ctor_set(v___x_4364_, 1, v_k_4368_);
lean_ctor_set(v___x_4364_, 0, v___x_4379_);
v___x_4388_ = v___x_4364_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_k_4368_);
lean_ctor_set(v_reuseFailAlloc_4389_, 2, v_v_4369_);
lean_ctor_set(v_reuseFailAlloc_4389_, 3, v___y_4381_);
lean_ctor_set(v_reuseFailAlloc_4389_, 4, v___x_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
v___jp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4394_ = lean_nat_add(v___x_4391_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec(v___x_4391_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_l_4370_);
lean_ctor_set(v___x_4344_, 3, v_l_4353_);
lean_ctor_set(v___x_4344_, 2, v_v_4352_);
lean_ctor_set(v___x_4344_, 1, v_k_4351_);
lean_ctor_set(v___x_4344_, 0, v___x_4394_);
v___x_4396_ = v___x_4344_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4394_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_k_4351_);
lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_v_4352_);
lean_ctor_set(v_reuseFailAlloc_4400_, 3, v_l_4353_);
lean_ctor_set(v_reuseFailAlloc_4400_, 4, v_l_4370_);
v___x_4396_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_nat_add(v___x_4348_, v_size_4349_);
if (lean_obj_tag(v_r_4371_) == 0)
{
lean_object* v_size_4398_; 
v_size_4398_ = lean_ctor_get(v_r_4371_, 0);
lean_inc(v_size_4398_);
v___y_4381_ = v___x_4396_;
v___y_4382_ = v___x_4397_;
v___y_4383_ = v_size_4398_;
goto v___jp_4380_;
}
else
{
lean_object* v___x_4399_; 
v___x_4399_ = lean_unsigned_to_nat(0u);
v___y_4381_ = v___x_4396_;
v___y_4382_ = v___x_4397_;
v___y_4383_ = v___x_4399_;
goto v___jp_4380_;
}
}
}
}
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
lean_del_object(v___x_4344_);
v___x_4409_ = lean_nat_add(v___x_4348_, v_size_4350_);
lean_dec(v_size_4350_);
v___x_4410_ = lean_nat_add(v___x_4409_, v_size_4349_);
lean_dec(v___x_4409_);
v___x_4411_ = lean_nat_add(v___x_4348_, v_size_4349_);
v___x_4412_ = lean_nat_add(v___x_4411_, v_size_4367_);
lean_dec(v___x_4411_);
lean_inc_ref(v_r_4342_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_r_4342_);
lean_ctor_set(v___x_4364_, 3, v_r_4354_);
lean_ctor_set(v___x_4364_, 2, v_v_4340_);
lean_ctor_set(v___x_4364_, 1, v_k_4339_);
lean_ctor_set(v___x_4364_, 0, v___x_4412_);
v___x_4414_ = v___x_4364_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4427_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4427_, 3, v_r_4354_);
lean_ctor_set(v_reuseFailAlloc_4427_, 4, v_r_4342_);
v___x_4414_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
v_isSharedCheck_4421_ = !lean_is_exclusive(v_r_4342_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; lean_object* v_unused_4426_; 
v_unused_4422_ = lean_ctor_get(v_r_4342_, 4);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_r_4342_, 3);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_r_4342_, 2);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_r_4342_, 1);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_r_4342_, 0);
lean_dec(v_unused_4426_);
v___x_4416_ = v_r_4342_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_dec(v_r_4342_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 4, v___x_4414_);
lean_ctor_set(v___x_4416_, 3, v_l_4353_);
lean_ctor_set(v___x_4416_, 2, v_v_4352_);
lean_ctor_set(v___x_4416_, 1, v_k_4351_);
lean_ctor_set(v___x_4416_, 0, v___x_4410_);
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_k_4351_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v_v_4352_);
lean_ctor_set(v_reuseFailAlloc_4420_, 3, v_l_4353_);
lean_ctor_set(v_reuseFailAlloc_4420_, 4, v___x_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4434_; 
v_l_4434_ = lean_ctor_get(v_impl_4347_, 3);
lean_inc(v_l_4434_);
if (lean_obj_tag(v_l_4434_) == 0)
{
lean_object* v_r_4435_; lean_object* v_k_4436_; lean_object* v_v_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4448_; 
v_r_4435_ = lean_ctor_get(v_impl_4347_, 4);
v_k_4436_ = lean_ctor_get(v_impl_4347_, 1);
v_v_4437_ = lean_ctor_get(v_impl_4347_, 2);
v_isSharedCheck_4448_ = !lean_is_exclusive(v_impl_4347_);
if (v_isSharedCheck_4448_ == 0)
{
lean_object* v_unused_4449_; lean_object* v_unused_4450_; 
v_unused_4449_ = lean_ctor_get(v_impl_4347_, 3);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_impl_4347_, 0);
lean_dec(v_unused_4450_);
v___x_4439_ = v_impl_4347_;
v_isShared_4440_ = v_isSharedCheck_4448_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_r_4435_);
lean_inc(v_v_4437_);
lean_inc(v_k_4436_);
lean_dec(v_impl_4347_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4448_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4443_; 
v___x_4441_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4435_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 3, v_r_4435_);
lean_ctor_set(v___x_4439_, 2, v_v_4340_);
lean_ctor_set(v___x_4439_, 1, v_k_4339_);
lean_ctor_set(v___x_4439_, 0, v___x_4348_);
v___x_4443_ = v___x_4439_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4447_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4447_, 3, v_r_4435_);
lean_ctor_set(v_reuseFailAlloc_4447_, 4, v_r_4435_);
v___x_4443_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
lean_object* v___x_4445_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v___x_4443_);
lean_ctor_set(v___x_4344_, 3, v_l_4434_);
lean_ctor_set(v___x_4344_, 2, v_v_4437_);
lean_ctor_set(v___x_4344_, 1, v_k_4436_);
lean_ctor_set(v___x_4344_, 0, v___x_4441_);
v___x_4445_ = v___x_4344_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4441_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_k_4436_);
lean_ctor_set(v_reuseFailAlloc_4446_, 2, v_v_4437_);
lean_ctor_set(v_reuseFailAlloc_4446_, 3, v_l_4434_);
lean_ctor_set(v_reuseFailAlloc_4446_, 4, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
else
{
lean_object* v_r_4451_; 
v_r_4451_ = lean_ctor_get(v_impl_4347_, 4);
lean_inc(v_r_4451_);
if (lean_obj_tag(v_r_4451_) == 0)
{
lean_object* v_k_4452_; lean_object* v_v_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4476_; 
v_k_4452_ = lean_ctor_get(v_impl_4347_, 1);
v_v_4453_ = lean_ctor_get(v_impl_4347_, 2);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_impl_4347_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; lean_object* v_unused_4478_; lean_object* v_unused_4479_; 
v_unused_4477_ = lean_ctor_get(v_impl_4347_, 4);
lean_dec(v_unused_4477_);
v_unused_4478_ = lean_ctor_get(v_impl_4347_, 3);
lean_dec(v_unused_4478_);
v_unused_4479_ = lean_ctor_get(v_impl_4347_, 0);
lean_dec(v_unused_4479_);
v___x_4455_ = v_impl_4347_;
v_isShared_4456_ = v_isSharedCheck_4476_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_v_4453_);
lean_inc(v_k_4452_);
lean_dec(v_impl_4347_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4476_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v_k_4457_; lean_object* v_v_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4472_; 
v_k_4457_ = lean_ctor_get(v_r_4451_, 1);
v_v_4458_ = lean_ctor_get(v_r_4451_, 2);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_r_4451_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; lean_object* v_unused_4474_; lean_object* v_unused_4475_; 
v_unused_4473_ = lean_ctor_get(v_r_4451_, 4);
lean_dec(v_unused_4473_);
v_unused_4474_ = lean_ctor_get(v_r_4451_, 3);
lean_dec(v_unused_4474_);
v_unused_4475_ = lean_ctor_get(v_r_4451_, 0);
lean_dec(v_unused_4475_);
v___x_4460_ = v_r_4451_;
v_isShared_4461_ = v_isSharedCheck_4472_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_v_4458_);
lean_inc(v_k_4457_);
lean_dec(v_r_4451_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4472_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4462_ = lean_unsigned_to_nat(3u);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 4, v_l_4434_);
lean_ctor_set(v___x_4460_, 3, v_l_4434_);
lean_ctor_set(v___x_4460_, 2, v_v_4453_);
lean_ctor_set(v___x_4460_, 1, v_k_4452_);
lean_ctor_set(v___x_4460_, 0, v___x_4348_);
v___x_4464_ = v___x_4460_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_k_4452_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_v_4453_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_l_4434_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_l_4434_);
v___x_4464_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
lean_object* v___x_4466_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 4, v_l_4434_);
lean_ctor_set(v___x_4455_, 2, v_v_4340_);
lean_ctor_set(v___x_4455_, 1, v_k_4339_);
lean_ctor_set(v___x_4455_, 0, v___x_4348_);
v___x_4466_ = v___x_4455_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4470_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4470_, 3, v_l_4434_);
lean_ctor_set(v_reuseFailAlloc_4470_, 4, v_l_4434_);
v___x_4466_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4468_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v___x_4466_);
lean_ctor_set(v___x_4344_, 3, v___x_4464_);
lean_ctor_set(v___x_4344_, 2, v_v_4458_);
lean_ctor_set(v___x_4344_, 1, v_k_4457_);
lean_ctor_set(v___x_4344_, 0, v___x_4462_);
v___x_4468_ = v___x_4344_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_k_4457_);
lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_v_4458_);
lean_ctor_set(v_reuseFailAlloc_4469_, 3, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4469_, 4, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
}
else
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = lean_unsigned_to_nat(2u);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_r_4451_);
lean_ctor_set(v___x_4344_, 3, v_impl_4347_);
lean_ctor_set(v___x_4344_, 0, v___x_4480_);
v___x_4482_ = v___x_4344_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v_impl_4347_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v_r_4451_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4485_; 
lean_dec(v_v_4340_);
lean_dec(v_k_4339_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 2, v_v_4336_);
lean_ctor_set(v___x_4344_, 1, v_k_4335_);
v___x_4485_ = v___x_4344_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_size_4338_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v_k_4335_);
lean_ctor_set(v_reuseFailAlloc_4486_, 2, v_v_4336_);
lean_ctor_set(v_reuseFailAlloc_4486_, 3, v_l_4341_);
lean_ctor_set(v_reuseFailAlloc_4486_, 4, v_r_4342_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
default: 
{
lean_object* v_impl_4487_; lean_object* v___x_4488_; 
lean_dec(v_size_4338_);
v_impl_4487_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4335_, v_v_4336_, v_r_4342_);
v___x_4488_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4341_) == 0)
{
lean_object* v_size_4489_; lean_object* v_size_4490_; lean_object* v_k_4491_; lean_object* v_v_4492_; lean_object* v_l_4493_; lean_object* v_r_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; 
v_size_4489_ = lean_ctor_get(v_l_4341_, 0);
v_size_4490_ = lean_ctor_get(v_impl_4487_, 0);
lean_inc(v_size_4490_);
v_k_4491_ = lean_ctor_get(v_impl_4487_, 1);
lean_inc(v_k_4491_);
v_v_4492_ = lean_ctor_get(v_impl_4487_, 2);
lean_inc(v_v_4492_);
v_l_4493_ = lean_ctor_get(v_impl_4487_, 3);
lean_inc(v_l_4493_);
v_r_4494_ = lean_ctor_get(v_impl_4487_, 4);
lean_inc(v_r_4494_);
v___x_4495_ = lean_unsigned_to_nat(3u);
v___x_4496_ = lean_nat_mul(v___x_4495_, v_size_4489_);
v___x_4497_ = lean_nat_dec_lt(v___x_4496_, v_size_4490_);
lean_dec(v___x_4496_);
if (v___x_4497_ == 0)
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4501_; 
lean_dec(v_r_4494_);
lean_dec(v_l_4493_);
lean_dec(v_v_4492_);
lean_dec(v_k_4491_);
v___x_4498_ = lean_nat_add(v___x_4488_, v_size_4489_);
v___x_4499_ = lean_nat_add(v___x_4498_, v_size_4490_);
lean_dec(v_size_4490_);
lean_dec(v___x_4498_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_impl_4487_);
lean_ctor_set(v___x_4344_, 0, v___x_4499_);
v___x_4501_ = v___x_4344_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_l_4341_);
lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_impl_4487_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
else
{
lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4566_; 
v_isSharedCheck_4566_ = !lean_is_exclusive(v_impl_4487_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; lean_object* v_unused_4568_; lean_object* v_unused_4569_; lean_object* v_unused_4570_; lean_object* v_unused_4571_; 
v_unused_4567_ = lean_ctor_get(v_impl_4487_, 4);
lean_dec(v_unused_4567_);
v_unused_4568_ = lean_ctor_get(v_impl_4487_, 3);
lean_dec(v_unused_4568_);
v_unused_4569_ = lean_ctor_get(v_impl_4487_, 2);
lean_dec(v_unused_4569_);
v_unused_4570_ = lean_ctor_get(v_impl_4487_, 1);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v_impl_4487_, 0);
lean_dec(v_unused_4571_);
v___x_4504_ = v_impl_4487_;
v_isShared_4505_ = v_isSharedCheck_4566_;
goto v_resetjp_4503_;
}
else
{
lean_dec(v_impl_4487_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4566_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v_size_4506_; lean_object* v_k_4507_; lean_object* v_v_4508_; lean_object* v_l_4509_; lean_object* v_r_4510_; lean_object* v_size_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v_size_4506_ = lean_ctor_get(v_l_4493_, 0);
v_k_4507_ = lean_ctor_get(v_l_4493_, 1);
v_v_4508_ = lean_ctor_get(v_l_4493_, 2);
v_l_4509_ = lean_ctor_get(v_l_4493_, 3);
v_r_4510_ = lean_ctor_get(v_l_4493_, 4);
v_size_4511_ = lean_ctor_get(v_r_4494_, 0);
v___x_4512_ = lean_unsigned_to_nat(2u);
v___x_4513_ = lean_nat_mul(v___x_4512_, v_size_4511_);
v___x_4514_ = lean_nat_dec_lt(v_size_4506_, v___x_4513_);
lean_dec(v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4542_; 
lean_inc(v_r_4510_);
lean_inc(v_l_4509_);
lean_inc(v_v_4508_);
lean_inc(v_k_4507_);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_l_4493_);
if (v_isSharedCheck_4542_ == 0)
{
lean_object* v_unused_4543_; lean_object* v_unused_4544_; lean_object* v_unused_4545_; lean_object* v_unused_4546_; lean_object* v_unused_4547_; 
v_unused_4543_ = lean_ctor_get(v_l_4493_, 4);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_l_4493_, 3);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_l_4493_, 2);
lean_dec(v_unused_4545_);
v_unused_4546_ = lean_ctor_get(v_l_4493_, 1);
lean_dec(v_unused_4546_);
v_unused_4547_ = lean_ctor_get(v_l_4493_, 0);
lean_dec(v_unused_4547_);
v___x_4516_ = v_l_4493_;
v_isShared_4517_ = v_isSharedCheck_4542_;
goto v_resetjp_4515_;
}
else
{
lean_dec(v_l_4493_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4542_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4532_; 
v___x_4518_ = lean_nat_add(v___x_4488_, v_size_4489_);
v___x_4519_ = lean_nat_add(v___x_4518_, v_size_4490_);
lean_dec(v_size_4490_);
if (lean_obj_tag(v_l_4509_) == 0)
{
lean_object* v_size_4540_; 
v_size_4540_ = lean_ctor_get(v_l_4509_, 0);
lean_inc(v_size_4540_);
v___y_4532_ = v_size_4540_;
goto v___jp_4531_;
}
else
{
lean_object* v___x_4541_; 
v___x_4541_ = lean_unsigned_to_nat(0u);
v___y_4532_ = v___x_4541_;
goto v___jp_4531_;
}
v___jp_4520_:
{
lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4524_ = lean_nat_add(v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec(v___y_4522_);
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 4, v_r_4494_);
lean_ctor_set(v___x_4516_, 3, v_r_4510_);
lean_ctor_set(v___x_4516_, 2, v_v_4492_);
lean_ctor_set(v___x_4516_, 1, v_k_4491_);
lean_ctor_set(v___x_4516_, 0, v___x_4524_);
v___x_4526_ = v___x_4516_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4530_, 1, v_k_4491_);
lean_ctor_set(v_reuseFailAlloc_4530_, 2, v_v_4492_);
lean_ctor_set(v_reuseFailAlloc_4530_, 3, v_r_4510_);
lean_ctor_set(v_reuseFailAlloc_4530_, 4, v_r_4494_);
v___x_4526_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
lean_object* v___x_4528_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 4, v___x_4526_);
lean_ctor_set(v___x_4504_, 3, v___y_4521_);
lean_ctor_set(v___x_4504_, 2, v_v_4508_);
lean_ctor_set(v___x_4504_, 1, v_k_4507_);
lean_ctor_set(v___x_4504_, 0, v___x_4519_);
v___x_4528_ = v___x_4504_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4519_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_k_4507_);
lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_v_4508_);
lean_ctor_set(v_reuseFailAlloc_4529_, 3, v___y_4521_);
lean_ctor_set(v_reuseFailAlloc_4529_, 4, v___x_4526_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
v___jp_4531_:
{
lean_object* v___x_4533_; lean_object* v___x_4535_; 
v___x_4533_ = lean_nat_add(v___x_4518_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec(v___x_4518_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_l_4509_);
lean_ctor_set(v___x_4344_, 0, v___x_4533_);
v___x_4535_ = v___x_4344_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4539_, 3, v_l_4341_);
lean_ctor_set(v_reuseFailAlloc_4539_, 4, v_l_4509_);
v___x_4535_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_nat_add(v___x_4488_, v_size_4511_);
if (lean_obj_tag(v_r_4510_) == 0)
{
lean_object* v_size_4537_; 
v_size_4537_ = lean_ctor_get(v_r_4510_, 0);
lean_inc(v_size_4537_);
v___y_4521_ = v___x_4535_;
v___y_4522_ = v___x_4536_;
v___y_4523_ = v_size_4537_;
goto v___jp_4520_;
}
else
{
lean_object* v___x_4538_; 
v___x_4538_ = lean_unsigned_to_nat(0u);
v___y_4521_ = v___x_4535_;
v___y_4522_ = v___x_4536_;
v___y_4523_ = v___x_4538_;
goto v___jp_4520_;
}
}
}
}
}
else
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4552_; 
lean_del_object(v___x_4344_);
v___x_4548_ = lean_nat_add(v___x_4488_, v_size_4489_);
v___x_4549_ = lean_nat_add(v___x_4548_, v_size_4490_);
lean_dec(v_size_4490_);
v___x_4550_ = lean_nat_add(v___x_4548_, v_size_4506_);
lean_dec(v___x_4548_);
lean_inc_ref(v_l_4341_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 4, v_l_4493_);
lean_ctor_set(v___x_4504_, 3, v_l_4341_);
lean_ctor_set(v___x_4504_, 2, v_v_4340_);
lean_ctor_set(v___x_4504_, 1, v_k_4339_);
lean_ctor_set(v___x_4504_, 0, v___x_4550_);
v___x_4552_ = v___x_4504_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4565_, 3, v_l_4341_);
lean_ctor_set(v_reuseFailAlloc_4565_, 4, v_l_4493_);
v___x_4552_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
v_isSharedCheck_4559_ = !lean_is_exclusive(v_l_4341_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; lean_object* v_unused_4561_; lean_object* v_unused_4562_; lean_object* v_unused_4563_; lean_object* v_unused_4564_; 
v_unused_4560_ = lean_ctor_get(v_l_4341_, 4);
lean_dec(v_unused_4560_);
v_unused_4561_ = lean_ctor_get(v_l_4341_, 3);
lean_dec(v_unused_4561_);
v_unused_4562_ = lean_ctor_get(v_l_4341_, 2);
lean_dec(v_unused_4562_);
v_unused_4563_ = lean_ctor_get(v_l_4341_, 1);
lean_dec(v_unused_4563_);
v_unused_4564_ = lean_ctor_get(v_l_4341_, 0);
lean_dec(v_unused_4564_);
v___x_4554_ = v_l_4341_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_dec(v_l_4341_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 4, v_r_4494_);
lean_ctor_set(v___x_4554_, 3, v___x_4552_);
lean_ctor_set(v___x_4554_, 2, v_v_4492_);
lean_ctor_set(v___x_4554_, 1, v_k_4491_);
lean_ctor_set(v___x_4554_, 0, v___x_4549_);
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_k_4491_);
lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_v_4492_);
lean_ctor_set(v_reuseFailAlloc_4558_, 3, v___x_4552_);
lean_ctor_set(v_reuseFailAlloc_4558_, 4, v_r_4494_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4572_; 
v_l_4572_ = lean_ctor_get(v_impl_4487_, 3);
lean_inc(v_l_4572_);
if (lean_obj_tag(v_l_4572_) == 0)
{
lean_object* v_r_4573_; lean_object* v_k_4574_; lean_object* v_v_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4598_; 
v_r_4573_ = lean_ctor_get(v_impl_4487_, 4);
v_k_4574_ = lean_ctor_get(v_impl_4487_, 1);
v_v_4575_ = lean_ctor_get(v_impl_4487_, 2);
v_isSharedCheck_4598_ = !lean_is_exclusive(v_impl_4487_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; lean_object* v_unused_4600_; 
v_unused_4599_ = lean_ctor_get(v_impl_4487_, 3);
lean_dec(v_unused_4599_);
v_unused_4600_ = lean_ctor_get(v_impl_4487_, 0);
lean_dec(v_unused_4600_);
v___x_4577_ = v_impl_4487_;
v_isShared_4578_ = v_isSharedCheck_4598_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_r_4573_);
lean_inc(v_v_4575_);
lean_inc(v_k_4574_);
lean_dec(v_impl_4487_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4598_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v_k_4579_; lean_object* v_v_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4594_; 
v_k_4579_ = lean_ctor_get(v_l_4572_, 1);
v_v_4580_ = lean_ctor_get(v_l_4572_, 2);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_l_4572_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; lean_object* v_unused_4596_; lean_object* v_unused_4597_; 
v_unused_4595_ = lean_ctor_get(v_l_4572_, 4);
lean_dec(v_unused_4595_);
v_unused_4596_ = lean_ctor_get(v_l_4572_, 3);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_l_4572_, 0);
lean_dec(v_unused_4597_);
v___x_4582_ = v_l_4572_;
v_isShared_4583_ = v_isSharedCheck_4594_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_v_4580_);
lean_inc(v_k_4579_);
lean_dec(v_l_4572_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4594_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v___x_4586_; 
v___x_4584_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4573_, 2);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 4, v_r_4573_);
lean_ctor_set(v___x_4582_, 3, v_r_4573_);
lean_ctor_set(v___x_4582_, 2, v_v_4340_);
lean_ctor_set(v___x_4582_, 1, v_k_4339_);
lean_ctor_set(v___x_4582_, 0, v___x_4488_);
v___x_4586_ = v___x_4582_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4488_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_r_4573_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_r_4573_);
v___x_4586_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4588_; 
lean_inc(v_r_4573_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 3, v_r_4573_);
lean_ctor_set(v___x_4577_, 0, v___x_4488_);
v___x_4588_ = v___x_4577_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4488_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_k_4574_);
lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_v_4575_);
lean_ctor_set(v_reuseFailAlloc_4592_, 3, v_r_4573_);
lean_ctor_set(v_reuseFailAlloc_4592_, 4, v_r_4573_);
v___x_4588_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_object* v___x_4590_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v___x_4588_);
lean_ctor_set(v___x_4344_, 3, v___x_4586_);
lean_ctor_set(v___x_4344_, 2, v_v_4580_);
lean_ctor_set(v___x_4344_, 1, v_k_4579_);
lean_ctor_set(v___x_4344_, 0, v___x_4584_);
v___x_4590_ = v___x_4344_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4591_, 1, v_k_4579_);
lean_ctor_set(v_reuseFailAlloc_4591_, 2, v_v_4580_);
lean_ctor_set(v_reuseFailAlloc_4591_, 3, v___x_4586_);
lean_ctor_set(v_reuseFailAlloc_4591_, 4, v___x_4588_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
}
else
{
lean_object* v_r_4601_; 
v_r_4601_ = lean_ctor_get(v_impl_4487_, 4);
lean_inc(v_r_4601_);
if (lean_obj_tag(v_r_4601_) == 0)
{
lean_object* v_k_4602_; lean_object* v_v_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4614_; 
v_k_4602_ = lean_ctor_get(v_impl_4487_, 1);
v_v_4603_ = lean_ctor_get(v_impl_4487_, 2);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_impl_4487_);
if (v_isSharedCheck_4614_ == 0)
{
lean_object* v_unused_4615_; lean_object* v_unused_4616_; lean_object* v_unused_4617_; 
v_unused_4615_ = lean_ctor_get(v_impl_4487_, 4);
lean_dec(v_unused_4615_);
v_unused_4616_ = lean_ctor_get(v_impl_4487_, 3);
lean_dec(v_unused_4616_);
v_unused_4617_ = lean_ctor_get(v_impl_4487_, 0);
lean_dec(v_unused_4617_);
v___x_4605_ = v_impl_4487_;
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_v_4603_);
lean_inc(v_k_4602_);
lean_dec(v_impl_4487_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4607_ = lean_unsigned_to_nat(3u);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 4, v_l_4572_);
lean_ctor_set(v___x_4605_, 2, v_v_4340_);
lean_ctor_set(v___x_4605_, 1, v_k_4339_);
lean_ctor_set(v___x_4605_, 0, v___x_4488_);
v___x_4609_ = v___x_4605_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4488_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4613_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4613_, 3, v_l_4572_);
lean_ctor_set(v_reuseFailAlloc_4613_, 4, v_l_4572_);
v___x_4609_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4611_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_r_4601_);
lean_ctor_set(v___x_4344_, 3, v___x_4609_);
lean_ctor_set(v___x_4344_, 2, v_v_4603_);
lean_ctor_set(v___x_4344_, 1, v_k_4602_);
lean_ctor_set(v___x_4344_, 0, v___x_4607_);
v___x_4611_ = v___x_4344_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_k_4602_);
lean_ctor_set(v_reuseFailAlloc_4612_, 2, v_v_4603_);
lean_ctor_set(v_reuseFailAlloc_4612_, 3, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4612_, 4, v_r_4601_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4618_ = lean_unsigned_to_nat(2u);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_impl_4487_);
lean_ctor_set(v___x_4344_, 3, v_r_4601_);
lean_ctor_set(v___x_4344_, 0, v___x_4618_);
v___x_4620_ = v___x_4344_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_k_4339_);
lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_v_4340_);
lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_r_4601_);
lean_ctor_set(v_reuseFailAlloc_4621_, 4, v_impl_4487_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
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
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = lean_unsigned_to_nat(1u);
v___x_4624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
lean_ctor_set(v___x_4624_, 1, v_k_4335_);
lean_ctor_set(v___x_4624_, 2, v_v_4336_);
lean_ctor_set(v___x_4624_, 3, v_t_4337_);
lean_ctor_set(v___x_4624_, 4, v_t_4337_);
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4625_, lean_object* v_k_4626_){
_start:
{
if (lean_obj_tag(v_t_4625_) == 0)
{
lean_object* v_k_4627_; lean_object* v_v_4628_; lean_object* v_l_4629_; lean_object* v_r_4630_; uint8_t v___x_4631_; 
v_k_4627_ = lean_ctor_get(v_t_4625_, 1);
v_v_4628_ = lean_ctor_get(v_t_4625_, 2);
v_l_4629_ = lean_ctor_get(v_t_4625_, 3);
v_r_4630_ = lean_ctor_get(v_t_4625_, 4);
v___x_4631_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4626_, v_k_4627_);
switch(v___x_4631_)
{
case 0:
{
v_t_4625_ = v_l_4629_;
goto _start;
}
case 1:
{
lean_object* v___x_4633_; 
lean_inc(v_v_4628_);
v___x_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4633_, 0, v_v_4628_);
return v___x_4633_;
}
default: 
{
v_t_4625_ = v_r_4630_;
goto _start;
}
}
}
else
{
lean_object* v___x_4635_; 
v___x_4635_ = lean_box(0);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4636_, lean_object* v_k_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4636_, v_k_4637_);
lean_dec(v_k_4637_);
lean_dec(v_t_4636_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4639_, lean_object* v_k_4640_, lean_object* v_v_4641_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4639_, v_k_4640_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4643_ = lean_box(0);
v___x_4644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4644_, 0, v_v_4641_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
v___x_4645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4640_, v___x_4644_, v_map_4639_);
return v___x_4645_;
}
else
{
lean_object* v_val_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v_val_4646_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_val_4646_);
lean_dec_ref_known(v___x_4642_, 1);
v___x_4647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4647_, 0, v_v_4641_);
lean_ctor_set(v___x_4647_, 1, v_val_4646_);
v___x_4648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4640_, v___x_4647_, v_map_4639_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4649_, lean_object* v_map_4650_, lean_object* v_k_4651_, lean_object* v_v_4652_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4650_, v_k_4651_, v_v_4652_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4654_, lean_object* v_t_4655_, lean_object* v_k_4656_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4655_, v_k_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4658_, lean_object* v_t_4659_, lean_object* v_k_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4658_, v_t_4659_, v_k_4660_);
lean_dec(v_k_4660_);
lean_dec(v_t_4659_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4662_, lean_object* v_k_4663_, lean_object* v_v_4664_, lean_object* v_t_4665_, lean_object* v_hl_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4663_, v_v_4664_, v_t_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4668_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = lean_box(1);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4670_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = lean_box(1);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4672_, lean_object* v_a_4673_, lean_object* v_b_4674_, lean_object* v_c_4675_){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v_a_4673_);
lean_ctor_set(v___x_4676_, 1, v_b_4674_);
v___x_4677_ = lean_apply_2(v_f_4672_, v___x_4676_, v_c_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4678_, lean_object* v_____do__lift_4679_){
_start:
{
lean_object* v_a_4680_; lean_object* v___x_4681_; 
v_a_4680_ = lean_ctor_get(v_____do__lift_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v_____do__lift_4679_);
v___x_4681_ = lean_apply_2(v_toPure_4678_, lean_box(0), v_a_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4682_, lean_object* v_m_4683_, lean_object* v_init_4684_, lean_object* v_f_4685_){
_start:
{
lean_object* v_toApplicative_4686_; lean_object* v_toBind_4687_; lean_object* v_toPure_4688_; lean_object* v___f_4689_; lean_object* v___x_4690_; lean_object* v___f_4691_; lean_object* v___x_4692_; 
v_toApplicative_4686_ = lean_ctor_get(v_inst_4682_, 0);
v_toBind_4687_ = lean_ctor_get(v_inst_4682_, 1);
lean_inc(v_toBind_4687_);
v_toPure_4688_ = lean_ctor_get(v_toApplicative_4686_, 1);
lean_inc(v_toPure_4688_);
v___f_4689_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4689_, 0, v_f_4685_);
v___x_4690_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4682_, v___f_4689_, v_init_4684_, v_m_4683_);
v___f_4691_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4691_, 0, v_toPure_4688_);
v___x_4692_ = lean_apply_4(v_toBind_4687_, lean_box(0), lean_box(0), v___x_4690_, v___f_4691_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4693_, lean_object* v_00_u03b1_4694_, lean_object* v_inst_4695_, lean_object* v_00_u03b2_4696_, lean_object* v_m_4697_, lean_object* v_init_4698_, lean_object* v_f_4699_){
_start:
{
lean_object* v_toApplicative_4700_; lean_object* v_toBind_4701_; lean_object* v_toPure_4702_; lean_object* v___f_4703_; lean_object* v___x_4704_; lean_object* v___f_4705_; lean_object* v___x_4706_; 
v_toApplicative_4700_ = lean_ctor_get(v_inst_4695_, 0);
v_toBind_4701_ = lean_ctor_get(v_inst_4695_, 1);
lean_inc(v_toBind_4701_);
v_toPure_4702_ = lean_ctor_get(v_toApplicative_4700_, 1);
lean_inc(v_toPure_4702_);
v___f_4703_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4703_, 0, v_f_4699_);
v___x_4704_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4695_, v___f_4703_, v_init_4698_, v_m_4697_);
v___f_4705_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4705_, 0, v_toPure_4702_);
v___x_4706_ = lean_apply_4(v_toBind_4701_, lean_box(0), lean_box(0), v___x_4704_, v___f_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4707_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4708_, 0, lean_box(0));
lean_closure_set(v___x_4708_, 1, lean_box(0));
lean_closure_set(v___x_4708_, 2, v_inst_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4709_, lean_object* v_00_u03b1_4710_, lean_object* v_inst_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4712_, 0, lean_box(0));
lean_closure_set(v___x_4712_, 1, lean_box(0));
lean_closure_set(v___x_4712_, 2, v_inst_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx(uint8_t v_x_4717_){
_start:
{
switch(v_x_4717_)
{
case 0:
{
lean_object* v___x_4718_; 
v___x_4718_ = lean_unsigned_to_nat(0u);
return v___x_4718_;
}
case 1:
{
lean_object* v___x_4719_; 
v___x_4719_ = lean_unsigned_to_nat(1u);
return v___x_4719_;
}
default: 
{
lean_object* v___x_4720_; 
v___x_4720_ = lean_unsigned_to_nat(2u);
return v___x_4720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___boxed(lean_object* v_x_4721_){
_start:
{
uint8_t v_x_boxed_4722_; lean_object* v_res_4723_; 
v_x_boxed_4722_ = lean_unbox(v_x_4721_);
v_res_4723_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_boxed_4722_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t v_x_4724_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object* v_x_4726_){
_start:
{
uint8_t v_x_4__boxed_4727_; lean_object* v_res_4728_; 
v_x_4__boxed_4727_ = lean_unbox(v_x_4726_);
v_res_4728_ = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(v_x_4__boxed_4727_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4729_){
_start:
{
lean_inc(v_k_4729_);
return v_k_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4730_);
lean_dec(v_k_4730_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4732_, lean_object* v_ctorIdx_4733_, uint8_t v_t_4734_, lean_object* v_h_4735_, lean_object* v_k_4736_){
_start:
{
lean_inc(v_k_4736_);
return v_k_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4737_, lean_object* v_ctorIdx_4738_, lean_object* v_t_4739_, lean_object* v_h_4740_, lean_object* v_k_4741_){
_start:
{
uint8_t v_t_boxed_4742_; lean_object* v_res_4743_; 
v_t_boxed_4742_ = lean_unbox(v_t_4739_);
v_res_4743_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4737_, v_ctorIdx_4738_, v_t_boxed_4742_, v_h_4740_, v_k_4741_);
lean_dec(v_k_4741_);
lean_dec(v_ctorIdx_4738_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4744_){
_start:
{
lean_inc(v_default_4744_);
return v_default_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4745_);
lean_dec(v_default_4745_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4747_, uint8_t v_t_4748_, lean_object* v_h_4749_, lean_object* v_default_4750_){
_start:
{
lean_inc(v_default_4750_);
return v_default_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4751_, lean_object* v_t_4752_, lean_object* v_h_4753_, lean_object* v_default_4754_){
_start:
{
uint8_t v_t_boxed_4755_; lean_object* v_res_4756_; 
v_t_boxed_4755_ = lean_unbox(v_t_4752_);
v_res_4756_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4751_, v_t_boxed_4755_, v_h_4753_, v_default_4754_);
lean_dec(v_default_4754_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4757_){
_start:
{
lean_inc(v_symbol_4757_);
return v_symbol_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4758_);
lean_dec(v_symbol_4758_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4760_, uint8_t v_t_4761_, lean_object* v_h_4762_, lean_object* v_symbol_4763_){
_start:
{
lean_inc(v_symbol_4763_);
return v_symbol_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4764_, lean_object* v_t_4765_, lean_object* v_h_4766_, lean_object* v_symbol_4767_){
_start:
{
uint8_t v_t_boxed_4768_; lean_object* v_res_4769_; 
v_t_boxed_4768_ = lean_unbox(v_t_4765_);
v_res_4769_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4764_, v_t_boxed_4768_, v_h_4766_, v_symbol_4767_);
lean_dec(v_symbol_4767_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4770_){
_start:
{
lean_inc(v_both_4770_);
return v_both_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4771_);
lean_dec(v_both_4771_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4773_, uint8_t v_t_4774_, lean_object* v_h_4775_, lean_object* v_both_4776_){
_start:
{
lean_inc(v_both_4776_);
return v_both_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4777_, lean_object* v_t_4778_, lean_object* v_h_4779_, lean_object* v_both_4780_){
_start:
{
uint8_t v_t_boxed_4781_; lean_object* v_res_4782_; 
v_t_boxed_4781_ = lean_unbox(v_t_4778_);
v_res_4782_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4777_, v_t_boxed_4781_, v_h_4779_, v_both_4780_);
lean_dec(v_both_4780_);
return v_res_4782_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4783_; 
v___x_4783_ = 0;
return v___x_4783_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4784_; 
v___x_4784_ = 0;
return v___x_4784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4785_, uint8_t v_y_4786_){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4787_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_x_4785_);
v___x_4788_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx(v_y_4786_);
v___x_4789_ = lean_nat_dec_eq(v___x_4787_, v___x_4788_);
lean_dec(v___x_4788_);
lean_dec(v___x_4787_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4790_, lean_object* v_y_4791_){
_start:
{
uint8_t v_x_17__boxed_4792_; uint8_t v_y_18__boxed_4793_; uint8_t v_res_4794_; lean_object* v_r_4795_; 
v_x_17__boxed_4792_ = lean_unbox(v_x_4790_);
v_y_18__boxed_4793_ = lean_unbox(v_y_4791_);
v_res_4794_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_17__boxed_4792_, v_y_18__boxed_4793_);
v_r_4795_ = lean_box(v_res_4794_);
return v_r_4795_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = lean_unsigned_to_nat(2u);
v___x_4808_ = lean_nat_to_int(v___x_4807_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4809_, lean_object* v_prec_4810_){
_start:
{
lean_object* v___y_4812_; lean_object* v___y_4819_; lean_object* v___y_4826_; 
switch(v_x_4809_)
{
case 0:
{
lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4832_ = lean_unsigned_to_nat(1024u);
v___x_4833_ = lean_nat_dec_le(v___x_4832_, v_prec_4810_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4812_ = v___x_4834_;
goto v___jp_4811_;
}
else
{
lean_object* v___x_4835_; 
v___x_4835_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4812_ = v___x_4835_;
goto v___jp_4811_;
}
}
case 1:
{
lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4836_ = lean_unsigned_to_nat(1024u);
v___x_4837_ = lean_nat_dec_le(v___x_4836_, v_prec_4810_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
v___x_4838_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4819_ = v___x_4838_;
goto v___jp_4818_;
}
else
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4819_ = v___x_4839_;
goto v___jp_4818_;
}
}
default: 
{
lean_object* v___x_4840_; uint8_t v___x_4841_; 
v___x_4840_ = lean_unsigned_to_nat(1024u);
v___x_4841_ = lean_nat_dec_le(v___x_4840_, v_prec_4810_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4826_ = v___x_4842_;
goto v___jp_4825_;
}
else
{
lean_object* v___x_4843_; 
v___x_4843_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4826_ = v___x_4843_;
goto v___jp_4825_;
}
}
}
v___jp_4811_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4813_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_4812_);
v___x_4814_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___y_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = 0;
v___x_4816_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4816_, 0, v___x_4814_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*1, v___x_4815_);
v___x_4817_ = l_Repr_addAppParen(v___x_4816_, v_prec_4810_);
return v___x_4817_;
}
v___jp_4818_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; uint8_t v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4820_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_4819_);
v___x_4821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___y_4819_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
v___x_4822_ = 0;
v___x_4823_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4823_, 0, v___x_4821_);
lean_ctor_set_uint8(v___x_4823_, sizeof(void*)*1, v___x_4822_);
v___x_4824_ = l_Repr_addAppParen(v___x_4823_, v_prec_4810_);
return v___x_4824_;
}
v___jp_4825_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4827_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_4826_);
v___x_4828_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___y_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = 0;
v___x_4830_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4830_, 0, v___x_4828_);
lean_ctor_set_uint8(v___x_4830_, sizeof(void*)*1, v___x_4829_);
v___x_4831_ = l_Repr_addAppParen(v___x_4830_, v_prec_4810_);
return v___x_4831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_4844_, lean_object* v_prec_4845_){
_start:
{
uint8_t v_x_175__boxed_4846_; lean_object* v_res_4847_; 
v_x_175__boxed_4846_ = lean_unbox(v_x_4844_);
v_res_4847_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_175__boxed_4846_, v_prec_4845_);
lean_dec(v_prec_4845_);
return v_res_4847_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4850_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
return v___x_4852_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4853_ = 0;
v___x_4854_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_4855_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_4856_ = lean_box(0);
v___x_4857_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
lean_ctor_set(v___x_4857_, 1, v___x_4855_);
lean_ctor_set(v___x_4857_, 2, v___x_4854_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*3, v___x_4853_);
return v___x_4857_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_4858_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_4860_, lean_object* v_c_4861_, lean_object* v_s_4862_, uint8_t v_behavior_4863_){
_start:
{
lean_object* v___x_4864_; lean_object* v_fst_4865_; lean_object* v_snd_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4908_; 
v___x_4864_ = l_Lean_Parser_peekToken(v_c_4861_, v_s_4862_);
v_fst_4865_ = lean_ctor_get(v___x_4864_, 0);
v_snd_4866_ = lean_ctor_get(v___x_4864_, 1);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4868_ = v___x_4864_;
v_isShared_4869_ = v_isSharedCheck_4908_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_snd_4866_);
lean_inc(v_fst_4865_);
lean_dec(v___x_4864_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4908_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v_n_4871_; 
if (lean_obj_tag(v_snd_4866_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
lean_del_object(v___x_4868_);
lean_dec(v_fst_4865_);
v_a_4883_ = lean_ctor_get(v_snd_4866_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v_snd_4866_, 1);
v___x_4884_ = lean_box(0);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v_a_4883_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
return v___x_4885_;
}
else
{
lean_object* v_a_4886_; 
v_a_4886_ = lean_ctor_get(v_snd_4866_, 0);
lean_inc(v_a_4886_);
lean_dec_ref_known(v_snd_4866_, 1);
switch(lean_obj_tag(v_a_4886_))
{
case 2:
{
lean_object* v_val_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v_val_4887_ = lean_ctor_get(v_a_4886_, 1);
lean_inc_ref(v_val_4887_);
lean_dec_ref_known(v_a_4886_, 2);
v___x_4888_ = lean_box(0);
v___x_4889_ = l_Lean_Name_str___override(v___x_4888_, v_val_4887_);
v_n_4871_ = v___x_4889_;
goto v___jp_4870_;
}
case 3:
{
switch(v_behavior_4863_)
{
case 0:
{
lean_dec_ref_known(v_a_4886_, 4);
goto v___jp_4881_;
}
case 1:
{
lean_object* v_val_4890_; lean_object* v___x_4891_; 
v_val_4890_ = lean_ctor_get(v_a_4886_, 2);
lean_inc(v_val_4890_);
lean_dec_ref_known(v_a_4886_, 4);
v___x_4891_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4860_, v_val_4890_);
lean_dec(v_val_4890_);
if (lean_obj_tag(v___x_4891_) == 0)
{
goto v___jp_4881_;
}
else
{
lean_object* v_val_4892_; lean_object* v___x_4893_; 
lean_del_object(v___x_4868_);
v_val_4892_ = lean_ctor_get(v___x_4891_, 0);
lean_inc(v_val_4892_);
lean_dec_ref_known(v___x_4891_, 1);
v___x_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4893_, 0, v_fst_4865_);
lean_ctor_set(v___x_4893_, 1, v_val_4892_);
return v___x_4893_;
}
}
default: 
{
lean_object* v_val_4894_; lean_object* v___x_4895_; 
v_val_4894_ = lean_ctor_get(v_a_4886_, 2);
lean_inc(v_val_4894_);
lean_dec_ref_known(v_a_4886_, 4);
v___x_4895_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4860_, v_val_4894_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_dec(v_val_4894_);
goto v___jp_4881_;
}
else
{
lean_object* v_val_4896_; lean_object* v___x_4897_; uint8_t v___x_4898_; 
lean_del_object(v___x_4868_);
v_val_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_val_4896_);
lean_dec_ref_known(v___x_4895_, 1);
v___x_4897_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_4898_ = lean_name_eq(v_val_4894_, v___x_4897_);
lean_dec(v_val_4894_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4860_, v___x_4897_);
if (lean_obj_tag(v___x_4899_) == 1)
{
lean_object* v_val_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v_val_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_val_4900_);
lean_dec_ref_known(v___x_4899_, 1);
v___x_4901_ = l_List_appendTR___redArg(v_val_4896_, v_val_4900_);
v___x_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4902_, 0, v_fst_4865_);
lean_ctor_set(v___x_4902_, 1, v___x_4901_);
return v___x_4902_;
}
else
{
lean_object* v___x_4903_; 
lean_dec(v___x_4899_);
v___x_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4903_, 0, v_fst_4865_);
lean_ctor_set(v___x_4903_, 1, v_val_4896_);
return v___x_4903_;
}
}
else
{
lean_object* v___x_4904_; 
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_fst_4865_);
lean_ctor_set(v___x_4904_, 1, v_val_4896_);
return v___x_4904_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_4905_; 
v_kind_4905_ = lean_ctor_get(v_a_4886_, 1);
lean_inc(v_kind_4905_);
lean_dec_ref_known(v_a_4886_, 3);
v_n_4871_ = v_kind_4905_;
goto v___jp_4870_;
}
default: 
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_dec(v_a_4886_);
lean_del_object(v___x_4868_);
v___x_4906_ = lean_box(0);
v___x_4907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4907_, 0, v_fst_4865_);
lean_ctor_set(v___x_4907_, 1, v___x_4906_);
return v___x_4907_;
}
}
}
v___jp_4870_:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4860_, v_n_4871_);
lean_dec(v_n_4871_);
if (lean_obj_tag(v___x_4872_) == 1)
{
lean_object* v_val_4873_; lean_object* v___x_4875_; 
v_val_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_val_4873_);
lean_dec_ref_known(v___x_4872_, 1);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 1, v_val_4873_);
v___x_4875_ = v___x_4868_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_fst_4865_);
lean_ctor_set(v_reuseFailAlloc_4876_, 1, v_val_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
else
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
lean_dec(v___x_4872_);
v___x_4877_ = lean_box(0);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 1, v___x_4877_);
v___x_4879_ = v___x_4868_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_fst_4865_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
v___jp_4881_:
{
lean_object* v___x_4882_; 
v___x_4882_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_4871_ = v___x_4882_;
goto v___jp_4870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_4909_, lean_object* v_c_4910_, lean_object* v_s_4911_, lean_object* v_behavior_4912_){
_start:
{
uint8_t v_behavior_boxed_4913_; lean_object* v_res_4914_; 
v_behavior_boxed_4913_ = lean_unbox(v_behavior_4912_);
v_res_4914_ = l_Lean_Parser_indexed___redArg(v_map_4909_, v_c_4910_, v_s_4911_, v_behavior_boxed_4913_);
lean_dec(v_map_4909_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_4915_, lean_object* v_map_4916_, lean_object* v_c_4917_, lean_object* v_s_4918_, uint8_t v_behavior_4919_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l_Lean_Parser_indexed___redArg(v_map_4916_, v_c_4917_, v_s_4918_, v_behavior_4919_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_4921_, lean_object* v_map_4922_, lean_object* v_c_4923_, lean_object* v_s_4924_, lean_object* v_behavior_4925_){
_start:
{
uint8_t v_behavior_boxed_4926_; lean_object* v_res_4927_; 
v_behavior_boxed_4926_ = lean_unbox(v_behavior_4925_);
v_res_4927_ = l_Lean_Parser_indexed(v_00_u03b1_4921_, v_map_4922_, v_c_4923_, v_s_4924_, v_behavior_boxed_4926_);
lean_dec(v_map_4922_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = l_Lean_Parser_whitespace(v___y_4929_, v___y_4930_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_4932_, v___y_4933_, v___y_4934_);
lean_dec(v_x_4932_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___f_4938_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_4939_ = lean_st_mk_ref(v___f_4938_);
v___x_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_4943_){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4945_ = lean_st_ref_get(v___x_4943_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_4947_);
lean_dec(v___x_4947_);
return v_res_4949_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___f_4951_; 
v___x_4950_ = l_Lean_Parser_categoryParserFnRef;
v___f_4951_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4951_, 0, v___x_4950_);
return v___f_4951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___f_4953_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_4954_ = lean_box(0);
v___x_4955_ = lean_box(2);
v___x_4956_ = l_Lean_registerEnvExtension___redArg(v___f_4953_, v___x_4954_, v___x_4955_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_4960_, v___y_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_4963_, v___y_4964_, v___y_4965_);
lean_dec_ref(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v_a_4963_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_4970_, lean_object* v_ctx_4971_, lean_object* v_s_4972_){
_start:
{
lean_object* v_toParserModuleContext_4973_; lean_object* v_env_4974_; lean_object* v___x_4975_; lean_object* v_asyncMode_4976_; lean_object* v___f_4977_; lean_object* v___x_4978_; lean_object* v___x_11__overap_4979_; lean_object* v___x_4980_; 
v_toParserModuleContext_4973_ = lean_ctor_get(v_ctx_4971_, 1);
v_env_4974_ = lean_ctor_get(v_toParserModuleContext_4973_, 0);
v___x_4975_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_4976_ = lean_ctor_get(v___x_4975_, 2);
v___f_4977_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_4978_ = lean_box(0);
lean_inc_ref(v_env_4974_);
v___x_11__overap_4979_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_4977_, v___x_4975_, v_env_4974_, v_asyncMode_4976_, v___x_4978_);
v___x_4980_ = lean_apply_3(v___x_11__overap_4979_, v_catName_4970_, v_ctx_4971_, v_s_4972_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_4981_, lean_object* v_x_4982_){
_start:
{
lean_object* v_quotDepth_4983_; uint8_t v_suppressInsideQuot_4984_; lean_object* v_savedPos_x3f_4985_; lean_object* v_forbiddenTk_x3f_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
v_quotDepth_4983_ = lean_ctor_get(v_x_4982_, 1);
v_suppressInsideQuot_4984_ = lean_ctor_get_uint8(v_x_4982_, sizeof(void*)*4);
v_savedPos_x3f_4985_ = lean_ctor_get(v_x_4982_, 2);
v_forbiddenTk_x3f_4986_ = lean_ctor_get(v_x_4982_, 3);
v_isSharedCheck_4993_ = !lean_is_exclusive(v_x_4982_);
if (v_isSharedCheck_4993_ == 0)
{
lean_object* v_unused_4994_; 
v_unused_4994_ = lean_ctor_get(v_x_4982_, 0);
lean_dec(v_unused_4994_);
v___x_4988_ = v_x_4982_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_forbiddenTk_x3f_4986_);
lean_inc(v_savedPos_x3f_4985_);
lean_inc(v_quotDepth_4983_);
lean_dec(v_x_4982_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v_prec_4981_);
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_prec_4981_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_quotDepth_4983_);
lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_savedPos_x3f_4985_);
lean_ctor_set(v_reuseFailAlloc_4992_, 3, v_forbiddenTk_x3f_4986_);
lean_ctor_set_uint8(v_reuseFailAlloc_4992_, sizeof(void*)*4, v_suppressInsideQuot_4984_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_4995_, lean_object* v_prec_4996_){
_start:
{
lean_object* v___f_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___f_4997_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_4997_, 0, v_prec_4996_);
v___x_4998_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_4995_);
v___x_4999_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_4999_, 0, v_catName_4995_);
v___x_5000_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_5000_, 0, v_catName_4995_);
lean_closure_set(v___x_5000_, 1, v___x_4999_);
v___x_5001_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5001_, 0, v___f_4997_);
lean_closure_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4998_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5006_){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5007_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5008_ = l_Lean_Parser_categoryParser(v___x_5007_, v_prec_5006_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5010_, lean_object* v_s_5011_){
_start:
{
lean_object* v_stxStack_5012_; lean_object* v_pos_5013_; lean_object* v_prev_5014_; uint8_t v___x_5015_; 
v_stxStack_5012_ = lean_ctor_get(v_s_5011_, 0);
v_pos_5013_ = lean_ctor_get(v_s_5011_, 2);
v_prev_5014_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5012_);
v___x_5015_ = l_Lean_Parser_checkTailNoWs(v_prev_5014_);
lean_dec(v_prev_5014_);
if (v___x_5015_ == 0)
{
return v_s_5011_;
}
else
{
lean_object* v_toInputContext_5016_; uint8_t v___x_5017_; 
v_toInputContext_5016_ = lean_ctor_get(v_c_5010_, 0);
v___x_5017_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5016_, v_pos_5013_);
if (v___x_5017_ == 0)
{
lean_object* v_inputString_5018_; uint32_t v_curr_5019_; uint32_t v___x_5020_; uint8_t v___x_5021_; 
v_inputString_5018_ = lean_ctor_get(v_toInputContext_5016_, 0);
v_curr_5019_ = lean_string_utf8_get_fast(v_inputString_5018_, v_pos_5013_);
v___x_5020_ = 58;
v___x_5021_ = lean_uint32_dec_eq(v_curr_5019_, v___x_5020_);
if (v___x_5021_ == 0)
{
return v_s_5011_;
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5022_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5023_ = lean_box(0);
v___x_5024_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5011_, v___x_5022_, v___x_5023_, v___x_5021_);
return v___x_5024_;
}
}
else
{
return v_s_5011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5025_, lean_object* v_s_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5025_, v_s_5026_);
lean_dec_ref(v_c_5025_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5040_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5041_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5042_ = l_Lean_addBuiltinDocString(v___x_5040_, v___x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5045_, lean_object* v_p_5046_, lean_object* v_c_5047_, lean_object* v_s_5048_){
_start:
{
lean_object* v___x_5049_; lean_object* v_errorMsg_5050_; 
v___x_5049_ = lean_apply_2(v_p_5046_, v_c_5047_, v_s_5048_);
v_errorMsg_5050_ = lean_ctor_get(v___x_5049_, 4);
lean_inc(v_errorMsg_5050_);
if (lean_obj_tag(v_errorMsg_5050_) == 1)
{
lean_object* v_val_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5081_; 
v_val_5051_ = lean_ctor_get(v_errorMsg_5050_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_errorMsg_5050_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5053_ = v_errorMsg_5050_;
v_isShared_5054_ = v_isSharedCheck_5081_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_val_5051_);
lean_dec(v_errorMsg_5050_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5081_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v_stxStack_5055_; lean_object* v_lhsPrec_5056_; lean_object* v_pos_5057_; lean_object* v_cache_5058_; lean_object* v_recoveredErrors_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5079_; 
v_stxStack_5055_ = lean_ctor_get(v___x_5049_, 0);
v_lhsPrec_5056_ = lean_ctor_get(v___x_5049_, 1);
v_pos_5057_ = lean_ctor_get(v___x_5049_, 2);
v_cache_5058_ = lean_ctor_get(v___x_5049_, 3);
v_recoveredErrors_5059_ = lean_ctor_get(v___x_5049_, 5);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5079_ == 0)
{
lean_object* v_unused_5080_; 
v_unused_5080_ = lean_ctor_get(v___x_5049_, 4);
lean_dec(v_unused_5080_);
v___x_5061_ = v___x_5049_;
v_isShared_5062_ = v_isSharedCheck_5079_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_recoveredErrors_5059_);
lean_inc(v_cache_5058_);
lean_inc(v_pos_5057_);
lean_inc(v_lhsPrec_5056_);
lean_inc(v_stxStack_5055_);
lean_dec(v___x_5049_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5079_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v_unexpectedTk_5063_; lean_object* v_unexpected_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5077_; 
v_unexpectedTk_5063_ = lean_ctor_get(v_val_5051_, 0);
v_unexpected_5064_ = lean_ctor_get(v_val_5051_, 1);
v_isSharedCheck_5077_ = !lean_is_exclusive(v_val_5051_);
if (v_isSharedCheck_5077_ == 0)
{
lean_object* v_unused_5078_; 
v_unused_5078_ = lean_ctor_get(v_val_5051_, 2);
lean_dec(v_unused_5078_);
v___x_5066_ = v_val_5051_;
v_isShared_5067_ = v_isSharedCheck_5077_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_unexpected_5064_);
lean_inc(v_unexpectedTk_5063_);
lean_dec(v_val_5051_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5077_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 2, v_expected_5045_);
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_unexpectedTk_5063_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v_unexpected_5064_);
lean_ctor_set(v_reuseFailAlloc_5076_, 2, v_expected_5045_);
v___x_5069_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5071_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 0, v___x_5069_);
v___x_5071_ = v___x_5053_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___x_5073_; 
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 4, v___x_5071_);
v___x_5073_ = v___x_5061_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_stxStack_5055_);
lean_ctor_set(v_reuseFailAlloc_5074_, 1, v_lhsPrec_5056_);
lean_ctor_set(v_reuseFailAlloc_5074_, 2, v_pos_5057_);
lean_ctor_set(v_reuseFailAlloc_5074_, 3, v_cache_5058_);
lean_ctor_set(v_reuseFailAlloc_5074_, 4, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5074_, 5, v_recoveredErrors_5059_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5050_);
lean_dec(v_expected_5045_);
return v___x_5049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5082_, lean_object* v_p_5083_){
_start:
{
lean_object* v_info_5084_; lean_object* v_fn_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5093_; 
v_info_5084_ = lean_ctor_get(v_p_5083_, 0);
v_fn_5085_ = lean_ctor_get(v_p_5083_, 1);
v_isSharedCheck_5093_ = !lean_is_exclusive(v_p_5083_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5087_ = v_p_5083_;
v_isShared_5088_ = v_isSharedCheck_5093_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_fn_5085_);
lean_inc(v_info_5084_);
lean_dec(v_p_5083_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5093_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5089_; lean_object* v___x_5091_; 
v___x_5089_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5089_, 0, v_expected_5082_);
lean_closure_set(v___x_5089_, 1, v_fn_5085_);
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 1, v___x_5089_);
v___x_5091_ = v___x_5087_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_info_5084_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5100_, lean_object* v_s_5101_){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = ((lean_object*)(l_Lean_Parser_pushNone___lam__0___closed__1));
v___x_5103_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5101_, v___x_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5104_, lean_object* v_s_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Lean_Parser_pushNone___lam__0(v_x_5104_, v_s_5105_);
lean_dec_ref(v_x_5104_);
return v_res_5106_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; 
v___x_5116_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5117_ = l_Lean_Parser_symbolNoAntiquot(v___x_5116_);
return v___x_5117_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5118_ = lean_unsigned_to_nat(0u);
v___x_5119_ = l_Lean_Parser_termParser(v___x_5118_);
return v___x_5119_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; 
v___x_5120_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5121_ = l_Lean_Parser_decQuotDepth(v___x_5120_);
return v___x_5121_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5122_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5123_ = l_Lean_Parser_symbolNoAntiquot(v___x_5122_);
return v___x_5123_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5124_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5125_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5126_ = l_Lean_Parser_andthen(v___x_5125_, v___x_5124_);
return v___x_5126_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5127_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5128_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5129_ = l_Lean_Parser_andthen(v___x_5128_, v___x_5127_);
return v___x_5129_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5130_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5131_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5132_ = l_Lean_Parser_node(v___x_5131_, v___x_5130_);
return v___x_5132_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5133_; 
v___x_5133_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5133_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5135_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5136_ = l_Lean_Parser_symbolNoAntiquot(v___x_5135_);
return v___x_5136_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5137_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5138_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5139_ = l_Lean_Parser_orelse(v___x_5138_, v___x_5137_);
return v___x_5139_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5140_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5141_ = l_Lean_Parser_identNoAntiquot;
v___x_5142_ = l_Lean_Parser_orelse(v___x_5141_, v___x_5140_);
return v___x_5142_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5143_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5145_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5146_ = l_Lean_Parser_checkNoWsBefore(v___x_5145_);
return v___x_5146_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5149_ = l_Lean_Parser_symbolNoAntiquot(v___x_5148_);
return v___x_5149_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5151_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5152_ = l_Lean_Parser_symbolNoAntiquot(v___x_5151_);
return v___x_5152_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5153_ = l_Lean_Parser_antiquotExpr;
v___x_5154_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5155_ = l_Lean_Parser_andthen(v___x_5154_, v___x_5153_);
return v___x_5155_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; 
v___x_5156_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5157_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5158_ = l_Lean_Parser_andthen(v___x_5157_, v___x_5156_);
return v___x_5158_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
v___x_5159_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5160_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5161_ = l_Lean_Parser_andthen(v___x_5160_, v___x_5159_);
return v___x_5161_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5162_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5163_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5164_ = l_Lean_Parser_andthen(v___x_5163_, v___x_5162_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5168_, lean_object* v_s_5169_){
_start:
{
lean_object* v_pos_5170_; lean_object* v_errorMsg_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; uint8_t v___x_5174_; 
v_pos_5170_ = lean_ctor_get(v_s_5169_, 2);
v_errorMsg_5171_ = lean_ctor_get(v_s_5169_, 4);
v___x_5172_ = lean_box(0);
lean_inc(v_errorMsg_5171_);
v___x_5173_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5171_, v___x_5172_);
v___x_5174_ = lean_bool_not(v___x_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; lean_object* v_fn_5176_; lean_object* v_iniSz_5177_; lean_object* v_s_5178_; lean_object* v_errorMsg_5179_; uint8_t v___x_5180_; uint8_t v___x_5181_; 
lean_inc(v_pos_5170_);
v___x_5175_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5176_ = lean_ctor_get(v___x_5175_, 1);
v_iniSz_5177_ = l_Lean_Parser_ParserState_stackSize(v_s_5169_);
lean_inc_ref(v_fn_5176_);
v_s_5178_ = lean_apply_2(v_fn_5176_, v_c_5168_, v_s_5169_);
v_errorMsg_5179_ = lean_ctor_get(v_s_5178_, 4);
lean_inc(v_errorMsg_5179_);
v___x_5180_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5179_, v___x_5172_);
v___x_5181_ = lean_bool_not(v___x_5180_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
lean_dec(v_pos_5170_);
v___x_5182_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5183_ = lean_unsigned_to_nat(1u);
v___x_5184_ = lean_nat_sub(v_iniSz_5177_, v___x_5183_);
lean_dec(v_iniSz_5177_);
v___x_5185_ = l_Lean_Parser_ParserState_mkNode(v_s_5178_, v___x_5182_, v___x_5184_);
lean_dec(v___x_5184_);
return v___x_5185_;
}
else
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_Parser_ParserState_restore(v_s_5178_, v_iniSz_5177_, v_pos_5170_);
lean_dec(v_iniSz_5177_);
return v___x_5186_;
}
}
else
{
lean_dec_ref(v_c_5168_);
return v_s_5169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_toInputContext_5190_; lean_object* v_s_5191_; lean_object* v_pos_5192_; lean_object* v_inputString_5193_; uint32_t v___x_5194_; uint32_t v___x_5195_; uint8_t v___x_5196_; 
v_toInputContext_5190_ = lean_ctor_get(v___y_5188_, 0);
lean_inc_ref(v___y_5188_);
v_s_5191_ = lean_apply_2(v_fn_5187_, v___y_5188_, v___y_5189_);
v_pos_5192_ = lean_ctor_get(v_s_5191_, 2);
lean_inc(v_pos_5192_);
v_inputString_5193_ = lean_ctor_get(v_toInputContext_5190_, 0);
v___x_5194_ = lean_string_utf8_get(v_inputString_5193_, v_pos_5192_);
lean_dec(v_pos_5192_);
v___x_5195_ = 37;
v___x_5196_ = lean_uint32_dec_eq(v___x_5194_, v___x_5195_);
if (v___x_5196_ == 0)
{
lean_dec_ref(v___y_5188_);
return v_s_5191_;
}
else
{
lean_object* v___x_5197_; 
v___x_5197_ = l_Lean_Parser_tokenAntiquotFn(v___y_5188_, v_s_5191_);
return v___x_5197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5198_){
_start:
{
lean_object* v_info_5199_; lean_object* v_fn_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5208_; 
v_info_5199_ = lean_ctor_get(v_p_5198_, 0);
v_fn_5200_ = lean_ctor_get(v_p_5198_, 1);
v_isSharedCheck_5208_ = !lean_is_exclusive(v_p_5198_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5202_ = v_p_5198_;
v_isShared_5203_ = v_isSharedCheck_5208_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_fn_5200_);
lean_inc(v_info_5199_);
lean_dec(v_p_5198_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5208_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___f_5204_; lean_object* v___x_5206_; 
v___f_5204_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5204_, 0, v_fn_5200_);
if (v_isShared_5203_ == 0)
{
lean_ctor_set(v___x_5202_, 1, v___f_5204_);
v___x_5206_ = v___x_5202_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_info_5199_);
lean_ctor_set(v_reuseFailAlloc_5207_, 1, v___f_5204_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5209_){
_start:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5210_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5209_);
v___x_5211_ = l_Lean_Parser_tokenWithAntiquot(v___x_5210_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5214_, uint8_t v_includeIdent_5215_){
_start:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5216_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5214_, v_includeIdent_5215_);
v___x_5217_ = l_Lean_Parser_tokenWithAntiquot(v___x_5216_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5218_, lean_object* v_includeIdent_5219_){
_start:
{
uint8_t v_includeIdent_boxed_5220_; lean_object* v_res_5221_; 
v_includeIdent_boxed_5220_ = lean_unbox(v_includeIdent_5219_);
v_res_5221_ = l_Lean_Parser_nonReservedSymbol(v_sym_5218_, v_includeIdent_boxed_5220_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5222_, lean_object* v_asciiSym_5223_){
_start:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5224_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5222_, v_asciiSym_5223_);
v___x_5225_ = l_Lean_Parser_tokenWithAntiquot(v___x_5224_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5226_, lean_object* v_asciiSym_5227_, uint8_t v_preserveForPP_5228_){
_start:
{
lean_object* v___x_5229_; 
v___x_5229_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5226_, v_asciiSym_5227_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5230_, lean_object* v_asciiSym_5231_, lean_object* v_preserveForPP_5232_){
_start:
{
uint8_t v_preserveForPP_boxed_5233_; lean_object* v_res_5234_; 
v_preserveForPP_boxed_5233_ = lean_unbox(v_preserveForPP_5232_);
v_res_5234_ = l_Lean_Parser_unicodeSymbol(v_sym_5230_, v_asciiSym_5231_, v_preserveForPP_boxed_5233_);
return v_res_5234_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5235_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5236_ = l_Lean_Parser_symbol(v___x_5235_);
return v___x_5236_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5237_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5238_ = lean_box(0);
v___x_5239_ = l_Lean_Parser_setExpected(v___x_5238_, v___x_5237_);
return v___x_5239_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5241_ = l_Lean_Parser_checkNoWsBefore(v___x_5240_);
return v___x_5241_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5242_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5243_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5244_ = l_Lean_Parser_andthen(v___x_5243_, v___x_5242_);
return v___x_5244_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5246_ = l_Lean_Parser_manyNoAntiquot(v___x_5245_);
return v___x_5246_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5248_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5249_ = l_Lean_Parser_checkNoWsBefore(v___x_5248_);
return v___x_5249_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; 
v___x_5258_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5259_ = l_Lean_Parser_symbol(v___x_5258_);
return v___x_5259_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5260_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5261_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5262_ = l_Lean_Parser_andthen(v___x_5261_, v___x_5260_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5266_, lean_object* v_kind_5267_, uint8_t v_anonymous_5268_, uint8_t v_isPseudoKind_5269_){
_start:
{
lean_object* v___y_5271_; lean_object* v___y_5272_; lean_object* v___y_5285_; 
if (v_isPseudoKind_5269_ == 0)
{
lean_object* v___x_5303_; 
v___x_5303_ = lean_box(0);
v___y_5285_ = v___x_5303_;
goto v___jp_5284_;
}
else
{
lean_object* v___x_5304_; 
v___x_5304_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5285_ = v___x_5304_;
goto v___jp_5284_;
}
v___jp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5273_ = l_Lean_Parser_maxPrec;
v___x_5274_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5275_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5276_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5277_ = l_Lean_Parser_antiquotExpr;
v___x_5278_ = l_Lean_Parser_andthen(v___x_5277_, v___y_5272_);
v___x_5279_ = l_Lean_Parser_andthen(v___x_5276_, v___x_5278_);
v___x_5280_ = l_Lean_Parser_andthen(v___x_5275_, v___x_5279_);
v___x_5281_ = l_Lean_Parser_andthen(v___x_5274_, v___x_5280_);
v___x_5282_ = l_Lean_Parser_atomic(v___x_5281_);
v___x_5283_ = l_Lean_Parser_leadingNode(v___y_5271_, v___x_5273_, v___x_5282_);
return v___x_5283_;
}
v___jp_5284_:
{
lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v_kind_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; uint8_t v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v_nameP_5300_; 
lean_inc(v___y_5285_);
v___x_5286_ = l_Lean_Name_append(v_kind_5267_, v___y_5285_);
v___x_5287_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5288_ = l_Lean_Name_append(v___x_5286_, v___x_5287_);
v___x_5289_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5290_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5291_ = lean_string_append(v___x_5290_, v_name_5266_);
v___x_5292_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5293_ = lean_string_append(v___x_5291_, v___x_5292_);
v___x_5294_ = l_Lean_Parser_checkNoWsBefore(v___x_5293_);
v___x_5295_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5296_ = 0;
v___x_5297_ = l_Lean_Parser_nonReservedSymbol(v_name_5266_, v___x_5296_);
v___x_5298_ = l_Lean_Parser_andthen(v___x_5295_, v___x_5297_);
v___x_5299_ = l_Lean_Parser_andthen(v___x_5294_, v___x_5298_);
v_nameP_5300_ = l_Lean_Parser_node(v___x_5289_, v___x_5299_);
if (v_anonymous_5268_ == 0)
{
v___y_5271_ = v_kind_5288_;
v___y_5272_ = v_nameP_5300_;
goto v___jp_5270_;
}
else
{
lean_object* v___x_5301_; lean_object* v___x_5302_; 
v___x_5301_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5302_ = l_Lean_Parser_orelse(v_nameP_5300_, v___x_5301_);
v___y_5271_ = v_kind_5288_;
v___y_5272_ = v___x_5302_;
goto v___jp_5270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5305_, lean_object* v_kind_5306_, lean_object* v_anonymous_5307_, lean_object* v_isPseudoKind_5308_){
_start:
{
uint8_t v_anonymous_boxed_5309_; uint8_t v_isPseudoKind_boxed_5310_; lean_object* v_res_5311_; 
v_anonymous_boxed_5309_ = lean_unbox(v_anonymous_5307_);
v_isPseudoKind_boxed_5310_ = lean_unbox(v_isPseudoKind_5308_);
v_res_5311_ = l_Lean_Parser_mkAntiquot(v_name_5305_, v_kind_5306_, v_anonymous_boxed_5309_, v_isPseudoKind_boxed_5310_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5319_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5320_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5321_ = l_Lean_addBuiltinDocString(v___x_5319_, v___x_5320_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5324_, lean_object* v_p_5325_, uint8_t v_isCatAntiquot_5326_, lean_object* v_c_5327_, lean_object* v_s_5328_){
_start:
{
lean_object* v_toInputContext_5329_; lean_object* v_pos_5330_; lean_object* v_inputString_5331_; uint32_t v___x_5332_; uint32_t v___x_5333_; uint8_t v___x_5334_; 
v_toInputContext_5329_ = lean_ctor_get(v_c_5327_, 0);
v_pos_5330_ = lean_ctor_get(v_s_5328_, 2);
v_inputString_5331_ = lean_ctor_get(v_toInputContext_5329_, 0);
v___x_5332_ = lean_string_utf8_get(v_inputString_5331_, v_pos_5330_);
v___x_5333_ = 36;
v___x_5334_ = lean_uint32_dec_eq(v___x_5332_, v___x_5333_);
if (v___x_5334_ == 0)
{
lean_object* v___x_5335_; 
lean_dec_ref(v_antiquotP_5324_);
v___x_5335_ = lean_apply_2(v_p_5325_, v_c_5327_, v_s_5328_);
return v___x_5335_;
}
else
{
if (v_isCatAntiquot_5326_ == 0)
{
uint8_t v___x_5336_; lean_object* v___x_5337_; 
v___x_5336_ = 1;
v___x_5337_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5324_, v_p_5325_, v___x_5336_, v_c_5327_, v_s_5328_);
return v___x_5337_;
}
else
{
uint8_t v___x_5338_; lean_object* v___x_5339_; 
v___x_5338_ = 0;
v___x_5339_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5324_, v_p_5325_, v___x_5338_, v_c_5327_, v_s_5328_);
return v___x_5339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5340_, lean_object* v_p_5341_, lean_object* v_isCatAntiquot_5342_, lean_object* v_c_5343_, lean_object* v_s_5344_){
_start:
{
uint8_t v_isCatAntiquot_boxed_5345_; lean_object* v_res_5346_; 
v_isCatAntiquot_boxed_5345_ = lean_unbox(v_isCatAntiquot_5342_);
v_res_5346_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5340_, v_p_5341_, v_isCatAntiquot_boxed_5345_, v_c_5343_, v_s_5344_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5347_, lean_object* v_p_5348_){
_start:
{
lean_object* v_info_5349_; lean_object* v_fn_5350_; lean_object* v_info_5351_; lean_object* v_fn_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5363_; 
v_info_5349_ = lean_ctor_get(v_antiquotP_5347_, 0);
lean_inc_ref(v_info_5349_);
v_fn_5350_ = lean_ctor_get(v_antiquotP_5347_, 1);
lean_inc_ref(v_fn_5350_);
lean_dec_ref(v_antiquotP_5347_);
v_info_5351_ = lean_ctor_get(v_p_5348_, 0);
v_fn_5352_ = lean_ctor_get(v_p_5348_, 1);
v_isSharedCheck_5363_ = !lean_is_exclusive(v_p_5348_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5354_ = v_p_5348_;
v_isShared_5355_ = v_isSharedCheck_5363_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_fn_5352_);
lean_inc(v_info_5351_);
lean_dec(v_p_5348_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5363_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5356_; uint8_t v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5356_ = l_Lean_Parser_orelseInfo(v_info_5349_, v_info_5351_);
v___x_5357_ = 0;
v___x_5358_ = lean_box(v___x_5357_);
v___x_5359_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5359_, 0, v_fn_5350_);
lean_closure_set(v___x_5359_, 1, v_fn_5352_);
lean_closure_set(v___x_5359_, 2, v___x_5358_);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 1, v___x_5359_);
lean_ctor_set(v___x_5354_, 0, v___x_5356_);
v___x_5361_ = v___x_5354_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5356_);
lean_ctor_set(v_reuseFailAlloc_5362_, 1, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5371_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5372_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5373_ = l_Lean_addBuiltinDocString(v___x_5371_, v___x_5372_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5376_){
_start:
{
lean_object* v_fn_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5385_; 
v_fn_5377_ = lean_ctor_get(v_p_5376_, 1);
v_isSharedCheck_5385_ = !lean_is_exclusive(v_p_5376_);
if (v_isSharedCheck_5385_ == 0)
{
lean_object* v_unused_5386_; 
v_unused_5386_ = lean_ctor_get(v_p_5376_, 0);
lean_dec(v_unused_5386_);
v___x_5379_ = v_p_5376_;
v_isShared_5380_ = v_isSharedCheck_5385_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_fn_5377_);
lean_dec(v_p_5376_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5385_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5381_; lean_object* v___x_5383_; 
v___x_5381_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 0, v___x_5381_);
v___x_5383_ = v___x_5379_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v___x_5381_);
lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_fn_5377_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5390_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5391_ = l_Lean_Parser_symbol(v___x_5390_);
return v___x_5391_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5393_ = l_Lean_Parser_symbol(v___x_5392_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5394_, lean_object* v_p_5395_, lean_object* v_suffix_5396_){
_start:
{
lean_object* v___x_5397_; lean_object* v_kind_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5397_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5398_ = l_Lean_Name_append(v_kind_5394_, v___x_5397_);
v___x_5399_ = l_Lean_Parser_maxPrec;
v___x_5400_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5401_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5402_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5403_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5404_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5405_ = l_Lean_Parser_node(v___x_5404_, v_p_5395_);
v___x_5406_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5407_ = l_Lean_Parser_andthen(v___x_5406_, v_suffix_5396_);
v___x_5408_ = l_Lean_Parser_andthen(v___x_5405_, v___x_5407_);
v___x_5409_ = l_Lean_Parser_andthen(v___x_5403_, v___x_5408_);
v___x_5410_ = l_Lean_Parser_andthen(v___x_5402_, v___x_5409_);
v___x_5411_ = l_Lean_Parser_andthen(v___x_5401_, v___x_5410_);
v___x_5412_ = l_Lean_Parser_andthen(v___x_5400_, v___x_5411_);
v___x_5413_ = l_Lean_Parser_atomic(v___x_5412_);
v___x_5414_ = l_Lean_Parser_leadingNode(v_kind_5398_, v___x_5399_, v___x_5413_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5422_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5423_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5424_ = l_Lean_addBuiltinDocString(v___x_5422_, v___x_5423_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5425_){
_start:
{
lean_object* v_res_5426_; 
v_res_5426_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5430_, lean_object* v_suffix_5431_, lean_object* v_c_5432_, lean_object* v_s_5433_){
_start:
{
lean_object* v_pos_5434_; lean_object* v_iniSz_5435_; lean_object* v_s_5436_; lean_object* v_stxStack_5437_; lean_object* v_errorMsg_5438_; lean_object* v___x_5439_; uint8_t v___x_5440_; uint8_t v___x_5441_; 
v_pos_5434_ = lean_ctor_get(v_s_5433_, 2);
lean_inc(v_pos_5434_);
v_iniSz_5435_ = l_Lean_Parser_ParserState_stackSize(v_s_5433_);
v_s_5436_ = lean_apply_2(v_suffix_5431_, v_c_5432_, v_s_5433_);
v_stxStack_5437_ = lean_ctor_get(v_s_5436_, 0);
lean_inc_ref(v_stxStack_5437_);
v_errorMsg_5438_ = lean_ctor_get(v_s_5436_, 4);
lean_inc(v_errorMsg_5438_);
v___x_5439_ = lean_box(0);
v___x_5440_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5438_, v___x_5439_);
v___x_5441_ = lean_bool_not(v___x_5440_);
if (v___x_5441_ == 0)
{
lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
lean_dec(v_iniSz_5435_);
lean_dec(v_pos_5434_);
v___x_5442_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5443_ = l_Lean_Name_append(v_kind_5430_, v___x_5442_);
v___x_5444_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5437_);
lean_dec_ref(v_stxStack_5437_);
v___x_5445_ = lean_unsigned_to_nat(2u);
v___x_5446_ = lean_nat_sub(v___x_5444_, v___x_5445_);
lean_dec(v___x_5444_);
v___x_5447_ = l_Lean_Parser_ParserState_mkNode(v_s_5436_, v___x_5443_, v___x_5446_);
lean_dec(v___x_5446_);
return v___x_5447_;
}
else
{
lean_object* v___x_5448_; 
lean_dec_ref(v_stxStack_5437_);
lean_dec(v_kind_5430_);
v___x_5448_ = l_Lean_Parser_ParserState_restore(v_s_5436_, v_iniSz_5435_, v_pos_5434_);
lean_dec(v_iniSz_5435_);
return v___x_5448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5449_, lean_object* v_kind_5450_, lean_object* v_fn_5451_, lean_object* v_c_5452_, lean_object* v_s_5453_){
_start:
{
lean_object* v_s_5454_; uint8_t v___y_5456_; lean_object* v_stxStack_5458_; lean_object* v_errorMsg_5459_; lean_object* v___x_5460_; uint8_t v___x_5461_; uint8_t v___x_5462_; uint8_t v___x_5463_; 
lean_inc_ref(v_c_5452_);
v_s_5454_ = lean_apply_2(v_fn_5449_, v_c_5452_, v_s_5453_);
v_stxStack_5458_ = lean_ctor_get(v_s_5454_, 0);
lean_inc_ref(v_stxStack_5458_);
v_errorMsg_5459_ = lean_ctor_get(v_s_5454_, 4);
lean_inc(v_errorMsg_5459_);
v___x_5460_ = lean_box(0);
v___x_5461_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5459_, v___x_5460_);
v___x_5462_ = lean_bool_not(v___x_5461_);
v___x_5463_ = lean_bool_not(v___x_5462_);
if (v___x_5463_ == 0)
{
lean_dec_ref(v_stxStack_5458_);
v___y_5456_ = v___x_5463_;
goto v___jp_5455_;
}
else
{
lean_object* v___x_5464_; uint8_t v___x_5465_; 
v___x_5464_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5458_);
lean_dec_ref(v_stxStack_5458_);
v___x_5465_ = l_Lean_Syntax_isAntiquots(v___x_5464_);
v___y_5456_ = v___x_5465_;
goto v___jp_5455_;
}
v___jp_5455_:
{
if (v___y_5456_ == 0)
{
lean_dec_ref(v_c_5452_);
lean_dec_ref(v_fn_5451_);
lean_dec(v_kind_5450_);
return v_s_5454_;
}
else
{
lean_object* v___x_5457_; 
v___x_5457_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5450_, v_fn_5451_, v_c_5452_, v_s_5454_);
return v___x_5457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5466_, lean_object* v_p_5467_, lean_object* v_suffix_5468_){
_start:
{
lean_object* v_info_5469_; lean_object* v_fn_5470_; lean_object* v_info_5471_; lean_object* v_fn_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5481_; 
v_info_5469_ = lean_ctor_get(v_p_5467_, 0);
lean_inc_ref(v_info_5469_);
v_fn_5470_ = lean_ctor_get(v_p_5467_, 1);
lean_inc_ref(v_fn_5470_);
lean_dec_ref(v_p_5467_);
v_info_5471_ = lean_ctor_get(v_suffix_5468_, 0);
v_fn_5472_ = lean_ctor_get(v_suffix_5468_, 1);
v_isSharedCheck_5481_ = !lean_is_exclusive(v_suffix_5468_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5474_ = v_suffix_5468_;
v_isShared_5475_ = v_isSharedCheck_5481_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_fn_5472_);
lean_inc(v_info_5471_);
lean_dec(v_suffix_5468_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5481_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___f_5476_; lean_object* v___x_5477_; lean_object* v___x_5479_; 
v___f_5476_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5476_, 0, v_fn_5470_);
lean_closure_set(v___f_5476_, 1, v_kind_5466_);
lean_closure_set(v___f_5476_, 2, v_fn_5472_);
v___x_5477_ = l_Lean_Parser_andthenInfo(v_info_5469_, v_info_5471_);
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 1, v___f_5476_);
lean_ctor_set(v___x_5474_, 0, v___x_5477_);
v___x_5479_ = v___x_5474_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5477_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v___f_5476_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; 
v___x_5489_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5490_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5491_ = l_Lean_addBuiltinDocString(v___x_5489_, v___x_5490_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5492_){
_start:
{
lean_object* v_res_5493_; 
v_res_5493_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5494_, lean_object* v_p_5495_, lean_object* v_suffix_5496_){
_start:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
lean_inc_ref(v_p_5495_);
v___x_5497_ = l_Lean_Parser_withoutInfo(v_p_5495_);
lean_inc_ref(v_suffix_5496_);
lean_inc(v_kind_5494_);
v___x_5498_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5494_, v___x_5497_, v_suffix_5496_);
v___x_5499_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5494_, v_p_5495_, v_suffix_5496_);
v___x_5500_ = l_Lean_Parser_withAntiquot(v___x_5498_, v___x_5499_);
return v___x_5500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5501_, lean_object* v_kind_5502_, lean_object* v_p_5503_, uint8_t v_anonymous_5504_){
_start:
{
uint8_t v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
v___x_5505_ = 0;
lean_inc(v_kind_5502_);
v___x_5506_ = l_Lean_Parser_mkAntiquot(v_name_5501_, v_kind_5502_, v_anonymous_5504_, v___x_5505_);
v___x_5507_ = l_Lean_Parser_node(v_kind_5502_, v_p_5503_);
v___x_5508_ = l_Lean_Parser_withAntiquot(v___x_5506_, v___x_5507_);
return v___x_5508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5509_, lean_object* v_kind_5510_, lean_object* v_p_5511_, lean_object* v_anonymous_5512_){
_start:
{
uint8_t v_anonymous_boxed_5513_; lean_object* v_res_5514_; 
v_anonymous_boxed_5513_ = lean_unbox(v_anonymous_5512_);
v_res_5514_ = l_Lean_Parser_nodeWithAntiquot(v_name_5509_, v_kind_5510_, v_p_5511_, v_anonymous_boxed_5513_);
return v_res_5514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5519_, lean_object* v_sep_5520_){
_start:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v_str_5525_; lean_object* v_startInclusive_5526_; lean_object* v_endExclusive_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5521_ = lean_unsigned_to_nat(0u);
v___x_5522_ = lean_string_utf8_byte_size(v_sep_5520_);
v___x_5523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5523_, 0, v_sep_5520_);
lean_ctor_set(v___x_5523_, 1, v___x_5521_);
lean_ctor_set(v___x_5523_, 2, v___x_5522_);
v___x_5524_ = l_String_Slice_trimAscii(v___x_5523_);
v_str_5525_ = lean_ctor_get(v___x_5524_, 0);
lean_inc_ref(v_str_5525_);
v_startInclusive_5526_ = lean_ctor_get(v___x_5524_, 1);
lean_inc(v_startInclusive_5526_);
v_endExclusive_5527_ = lean_ctor_get(v___x_5524_, 2);
lean_inc(v_endExclusive_5527_);
lean_dec_ref(v___x_5524_);
v___x_5528_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5529_ = lean_string_utf8_extract(v_str_5525_, v_startInclusive_5526_, v_endExclusive_5527_);
lean_dec(v_endExclusive_5527_);
lean_dec(v_startInclusive_5526_);
lean_dec_ref(v_str_5525_);
v___x_5530_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5531_ = lean_string_append(v___x_5529_, v___x_5530_);
v___x_5532_ = l_Lean_Parser_symbol(v___x_5531_);
v___x_5533_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5528_, v_p_5519_, v___x_5532_);
return v___x_5533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5534_, lean_object* v_sep_5535_, lean_object* v_psep_5536_, uint8_t v_allowTrailingSep_5537_){
_start:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
v___x_5538_ = l_Lean_Parser_sepByElemParser(v_p_5534_, v_sep_5535_);
v___x_5539_ = l_Lean_Parser_sepByNoAntiquot(v___x_5538_, v_psep_5536_, v_allowTrailingSep_5537_);
return v___x_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5540_, lean_object* v_sep_5541_, lean_object* v_psep_5542_, lean_object* v_allowTrailingSep_5543_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5544_; lean_object* v_res_5545_; 
v_allowTrailingSep_boxed_5544_ = lean_unbox(v_allowTrailingSep_5543_);
v_res_5545_ = l_Lean_Parser_sepBy(v_p_5540_, v_sep_5541_, v_psep_5542_, v_allowTrailingSep_boxed_5544_);
return v_res_5545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5546_, lean_object* v_sep_5547_, lean_object* v_psep_5548_, uint8_t v_allowTrailingSep_5549_){
_start:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = l_Lean_Parser_sepByElemParser(v_p_5546_, v_sep_5547_);
v___x_5551_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5550_, v_psep_5548_, v_allowTrailingSep_5549_);
return v___x_5551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5552_, lean_object* v_sep_5553_, lean_object* v_psep_5554_, lean_object* v_allowTrailingSep_5555_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5556_; lean_object* v_res_5557_; 
v_allowTrailingSep_boxed_5556_ = lean_unbox(v_allowTrailingSep_5555_);
v_res_5557_ = l_Lean_Parser_sepBy1(v_p_5552_, v_sep_5553_, v_psep_5554_, v_allowTrailingSep_boxed_5556_);
return v_res_5557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5558_, lean_object* v_iniSz_5559_){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; uint8_t v___x_5563_; 
v___x_5560_ = l_Lean_Parser_ParserState_stackSize(v_s_5558_);
v___x_5561_ = lean_unsigned_to_nat(1u);
v___x_5562_ = lean_nat_add(v_iniSz_5559_, v___x_5561_);
v___x_5563_ = lean_nat_dec_eq(v___x_5560_, v___x_5562_);
lean_dec(v___x_5562_);
lean_dec(v___x_5560_);
if (v___x_5563_ == 0)
{
lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5564_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5565_ = l_Lean_Parser_ParserState_mkNode(v_s_5558_, v___x_5564_, v_iniSz_5559_);
return v___x_5565_;
}
else
{
return v_s_5558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5566_, lean_object* v_iniSz_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5566_, v_iniSz_5567_);
lean_dec(v_iniSz_5567_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5569_, lean_object* v_tables_5570_, uint8_t v_behavior_5571_, lean_object* v_c_5572_, lean_object* v_s_5573_){
_start:
{
lean_object* v_leadingTable_5574_; lean_object* v_leadingParsers_5575_; lean_object* v_iniSz_5576_; lean_object* v___x_5577_; lean_object* v_fst_5578_; lean_object* v_snd_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5602_; 
v_leadingTable_5574_ = lean_ctor_get(v_tables_5570_, 0);
lean_inc(v_leadingTable_5574_);
v_leadingParsers_5575_ = lean_ctor_get(v_tables_5570_, 1);
lean_inc(v_leadingParsers_5575_);
lean_dec_ref(v_tables_5570_);
v_iniSz_5576_ = l_Lean_Parser_ParserState_stackSize(v_s_5573_);
lean_inc_ref(v_c_5572_);
v___x_5577_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5574_, v_c_5572_, v_s_5573_, v_behavior_5571_);
lean_dec(v_leadingTable_5574_);
v_fst_5578_ = lean_ctor_get(v___x_5577_, 0);
v_snd_5579_ = lean_ctor_get(v___x_5577_, 1);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5581_ = v___x_5577_;
v_isShared_5582_ = v_isSharedCheck_5602_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_snd_5579_);
lean_inc(v_fst_5578_);
lean_dec(v___x_5577_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5602_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v_errorMsg_5583_; lean_object* v___x_5584_; uint8_t v___x_5585_; uint8_t v___x_5586_; 
v_errorMsg_5583_ = lean_ctor_get(v_fst_5578_, 4);
v___x_5584_ = lean_box(0);
lean_inc(v_errorMsg_5583_);
v___x_5585_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5583_, v___x_5584_);
v___x_5586_ = lean_bool_not(v___x_5585_);
if (v___x_5586_ == 0)
{
lean_object* v_ps_5587_; uint8_t v___x_5588_; 
v_ps_5587_ = l_List_appendTR___redArg(v_leadingParsers_5575_, v_snd_5579_);
v___x_5588_ = l_List_isEmpty___redArg(v_ps_5587_);
if (v___x_5588_ == 0)
{
lean_object* v_s_5589_; lean_object* v___x_5590_; 
lean_del_object(v___x_5581_);
lean_dec(v_kind_5569_);
v_s_5589_ = l_Lean_Parser_longestMatchFn(v___x_5584_, v_ps_5587_, v_c_5572_, v_fst_5578_);
v___x_5590_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5589_, v_iniSz_5576_);
lean_dec(v_iniSz_5576_);
return v___x_5590_;
}
else
{
lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5594_; 
lean_dec(v_ps_5587_);
lean_dec(v_iniSz_5576_);
v___x_5591_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5569_, v___x_5588_);
v___x_5592_ = lean_box(0);
lean_inc_ref(v___x_5591_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set_tag(v___x_5581_, 1);
lean_ctor_set(v___x_5581_, 1, v___x_5592_);
lean_ctor_set(v___x_5581_, 0, v___x_5591_);
v___x_5594_ = v___x_5581_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v___x_5592_);
v___x_5594_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
lean_object* v_s_5595_; lean_object* v_errorMsg_5596_; uint8_t v___x_5597_; uint8_t v___x_5598_; 
v_s_5595_ = l_Lean_Parser_tokenFn(v___x_5594_, v_c_5572_, v_fst_5578_);
v_errorMsg_5596_ = lean_ctor_get(v_s_5595_, 4);
lean_inc(v_errorMsg_5596_);
v___x_5597_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5596_, v___x_5584_);
v___x_5598_ = lean_bool_not(v___x_5597_);
if (v___x_5598_ == 0)
{
lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5599_ = lean_unsigned_to_nat(0u);
v___x_5600_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5595_, v___x_5591_, v___x_5599_);
return v___x_5600_;
}
else
{
lean_dec_ref(v___x_5591_);
return v_s_5595_;
}
}
}
}
else
{
lean_del_object(v___x_5581_);
lean_dec(v_snd_5579_);
lean_dec(v_iniSz_5576_);
lean_dec(v_leadingParsers_5575_);
lean_dec_ref(v_c_5572_);
lean_dec(v_kind_5569_);
return v_fst_5578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5603_, lean_object* v_tables_5604_, lean_object* v_behavior_5605_, lean_object* v_c_5606_, lean_object* v_s_5607_){
_start:
{
uint8_t v_behavior_boxed_5608_; lean_object* v_res_5609_; 
v_behavior_boxed_5608_ = lean_unbox(v_behavior_5605_);
v_res_5609_ = l_Lean_Parser_leadingParserAux(v_kind_5603_, v_tables_5604_, v_behavior_boxed_5608_, v_c_5606_, v_s_5607_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5610_, lean_object* v_tables_5611_, uint8_t v_behavior_5612_, lean_object* v_antiquotParser_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_){
_start:
{
lean_object* v___x_5616_; lean_object* v___x_5617_; uint8_t v___x_5618_; lean_object* v___x_5619_; 
v___x_5616_ = lean_box(v_behavior_5612_);
v___x_5617_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5617_, 0, v_kind_5610_);
lean_closure_set(v___x_5617_, 1, v_tables_5611_);
lean_closure_set(v___x_5617_, 2, v___x_5616_);
v___x_5618_ = 1;
v___x_5619_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5613_, v___x_5617_, v___x_5618_, v_a_5614_, v_a_5615_);
return v___x_5619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5620_, lean_object* v_tables_5621_, lean_object* v_behavior_5622_, lean_object* v_antiquotParser_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_){
_start:
{
uint8_t v_behavior_boxed_5626_; lean_object* v_res_5627_; 
v_behavior_boxed_5626_ = lean_unbox(v_behavior_5622_);
v_res_5627_ = l_Lean_Parser_leadingParser(v_kind_5620_, v_tables_5621_, v_behavior_boxed_5626_, v_antiquotParser_5623_, v_a_5624_, v_a_5625_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5628_, lean_object* v_left_5629_, lean_object* v_ps_5630_, lean_object* v_c_5631_, lean_object* v_s_5632_){
_start:
{
lean_object* v_trailingParsers_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; 
v_trailingParsers_5633_ = lean_ctor_get(v_tables_5628_, 3);
lean_inc(v_trailingParsers_5633_);
lean_dec_ref(v_tables_5628_);
v___x_5634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5634_, 0, v_left_5629_);
v___x_5635_ = l_List_appendTR___redArg(v_ps_5630_, v_trailingParsers_5633_);
v___x_5636_ = l_Lean_Parser_longestMatchFn(v___x_5634_, v___x_5635_, v_c_5631_, v_s_5632_);
return v___x_5636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5637_, lean_object* v_c_5638_, lean_object* v_s_5639_){
_start:
{
lean_object* v_pos_5640_; lean_object* v_trailingTable_5641_; lean_object* v_trailingParsers_5642_; lean_object* v_iniSz_5643_; uint8_t v___x_5644_; lean_object* v___x_5645_; lean_object* v_fst_5646_; lean_object* v_snd_5647_; lean_object* v_stxStack_5648_; lean_object* v_errorMsg_5649_; uint8_t v___y_5651_; lean_object* v___x_5666_; uint8_t v___x_5667_; uint8_t v___x_5668_; 
v_pos_5640_ = lean_ctor_get(v_s_5639_, 2);
lean_inc(v_pos_5640_);
v_trailingTable_5641_ = lean_ctor_get(v_tables_5637_, 2);
v_trailingParsers_5642_ = lean_ctor_get(v_tables_5637_, 3);
v_iniSz_5643_ = l_Lean_Parser_ParserState_stackSize(v_s_5639_);
v___x_5644_ = 0;
lean_inc_ref(v_c_5638_);
v___x_5645_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5641_, v_c_5638_, v_s_5639_, v___x_5644_);
v_fst_5646_ = lean_ctor_get(v___x_5645_, 0);
lean_inc(v_fst_5646_);
v_snd_5647_ = lean_ctor_get(v___x_5645_, 1);
lean_inc(v_snd_5647_);
lean_dec_ref(v___x_5645_);
v_stxStack_5648_ = lean_ctor_get(v_fst_5646_, 0);
v_errorMsg_5649_ = lean_ctor_get(v_fst_5646_, 4);
v___x_5666_ = lean_box(0);
lean_inc(v_errorMsg_5649_);
v___x_5667_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5649_, v___x_5666_);
v___x_5668_ = lean_bool_not(v___x_5667_);
if (v___x_5668_ == 0)
{
uint8_t v___x_5669_; 
v___x_5669_ = l_List_isEmpty___redArg(v_snd_5647_);
if (v___x_5669_ == 0)
{
v___y_5651_ = v___x_5669_;
goto v___jp_5650_;
}
else
{
uint8_t v___x_5670_; 
v___x_5670_ = l_List_isEmpty___redArg(v_trailingParsers_5642_);
v___y_5651_ = v___x_5670_;
goto v___jp_5650_;
}
}
else
{
lean_object* v___x_5671_; 
lean_dec(v_snd_5647_);
lean_dec_ref(v_c_5638_);
lean_dec_ref(v_tables_5637_);
v___x_5671_ = l_Lean_Parser_ParserState_restore(v_fst_5646_, v_iniSz_5643_, v_pos_5640_);
lean_dec(v_iniSz_5643_);
return v___x_5671_;
}
v___jp_5650_:
{
if (v___y_5651_ == 0)
{
lean_object* v_left_5652_; lean_object* v_s_5653_; lean_object* v_s_5654_; lean_object* v_pos_5655_; lean_object* v_errorMsg_5656_; lean_object* v___x_5657_; uint8_t v___x_5658_; uint8_t v___x_5659_; 
v_left_5652_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5648_);
v_s_5653_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5646_);
lean_inc_ref(v_c_5638_);
lean_inc(v_left_5652_);
lean_inc_ref(v_tables_5637_);
v_s_5654_ = l_Lean_Parser_trailingLoopStep(v_tables_5637_, v_left_5652_, v_snd_5647_, v_c_5638_, v_s_5653_);
v_pos_5655_ = lean_ctor_get(v_s_5654_, 2);
lean_inc(v_pos_5655_);
v_errorMsg_5656_ = lean_ctor_get(v_s_5654_, 4);
lean_inc(v_errorMsg_5656_);
v___x_5657_ = lean_box(0);
v___x_5658_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5656_, v___x_5657_);
v___x_5659_ = lean_bool_not(v___x_5658_);
if (v___x_5659_ == 0)
{
lean_dec(v_pos_5655_);
lean_dec(v_left_5652_);
lean_dec(v_iniSz_5643_);
lean_dec(v_pos_5640_);
v_s_5639_ = v_s_5654_;
goto _start;
}
else
{
uint8_t v___x_5661_; 
lean_dec_ref(v_c_5638_);
lean_dec_ref(v_tables_5637_);
v___x_5661_ = lean_nat_dec_eq(v_pos_5655_, v_pos_5640_);
lean_dec(v_pos_5655_);
if (v___x_5661_ == 0)
{
lean_dec(v_left_5652_);
lean_dec(v_iniSz_5643_);
lean_dec(v_pos_5640_);
return v_s_5654_;
}
else
{
lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5662_ = lean_unsigned_to_nat(1u);
v___x_5663_ = lean_nat_sub(v_iniSz_5643_, v___x_5662_);
lean_dec(v_iniSz_5643_);
v___x_5664_ = l_Lean_Parser_ParserState_restore(v_s_5654_, v___x_5663_, v_pos_5640_);
lean_dec(v___x_5663_);
v___x_5665_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5664_, v_left_5652_);
return v___x_5665_;
}
}
}
else
{
lean_dec(v_snd_5647_);
lean_dec(v_iniSz_5643_);
lean_dec(v_pos_5640_);
lean_dec_ref(v_c_5638_);
lean_dec_ref(v_tables_5637_);
return v_fst_5646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5672_, lean_object* v_tables_5673_, uint8_t v_behavior_5674_, lean_object* v_antiquotParser_5675_, lean_object* v_c_5676_, lean_object* v_s_5677_){
_start:
{
lean_object* v_s_5678_; lean_object* v_errorMsg_5679_; lean_object* v___x_5680_; uint8_t v___x_5681_; uint8_t v___x_5682_; 
lean_inc_ref(v_c_5676_);
lean_inc_ref(v_tables_5673_);
v_s_5678_ = l_Lean_Parser_leadingParser(v_kind_5672_, v_tables_5673_, v_behavior_5674_, v_antiquotParser_5675_, v_c_5676_, v_s_5677_);
v_errorMsg_5679_ = lean_ctor_get(v_s_5678_, 4);
lean_inc(v_errorMsg_5679_);
v___x_5680_ = lean_box(0);
v___x_5681_ = l_Option_instBEq_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5679_, v___x_5680_);
v___x_5682_ = lean_bool_not(v___x_5681_);
if (v___x_5682_ == 0)
{
lean_object* v___x_5683_; 
v___x_5683_ = l_Lean_Parser_trailingLoop(v_tables_5673_, v_c_5676_, v_s_5678_);
return v___x_5683_;
}
else
{
lean_dec_ref(v_c_5676_);
lean_dec_ref(v_tables_5673_);
return v_s_5678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5684_, lean_object* v_tables_5685_, lean_object* v_behavior_5686_, lean_object* v_antiquotParser_5687_, lean_object* v_c_5688_, lean_object* v_s_5689_){
_start:
{
uint8_t v_behavior_boxed_5690_; lean_object* v_res_5691_; 
v_behavior_boxed_5690_ = lean_unbox(v_behavior_5686_);
v_res_5691_ = l_Lean_Parser_prattParser(v_kind_5684_, v_tables_5685_, v_behavior_boxed_5690_, v_antiquotParser_5687_, v_c_5688_, v_s_5689_);
return v_res_5691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5696_, lean_object* v_s_5697_){
_start:
{
lean_object* v_toInputContext_5698_; lean_object* v_pos_5699_; lean_object* v_inputString_5700_; lean_object* v___f_5701_; lean_object* v_initStackSz_5702_; uint32_t v_curr_5707_; uint8_t v___y_5709_; uint32_t v___x_5716_; uint8_t v___x_5717_; 
v_toInputContext_5698_ = lean_ctor_get(v_c_5696_, 0);
v_pos_5699_ = lean_ctor_get(v_s_5697_, 2);
lean_inc(v_pos_5699_);
v_inputString_5700_ = lean_ctor_get(v_toInputContext_5698_, 0);
v___f_5701_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_initStackSz_5702_ = l_Lean_Parser_ParserState_stackSize(v_s_5697_);
v_curr_5707_ = lean_string_utf8_get(v_inputString_5700_, v_pos_5699_);
v___x_5716_ = 48;
v___x_5717_ = lean_uint32_dec_le(v___x_5716_, v_curr_5707_);
if (v___x_5717_ == 0)
{
v___y_5709_ = v___x_5717_;
goto v___jp_5708_;
}
else
{
uint32_t v___x_5718_; uint8_t v___x_5719_; 
v___x_5718_ = 57;
v___x_5719_ = lean_uint32_dec_le(v_curr_5707_, v___x_5718_);
v___y_5709_ = v___x_5719_;
goto v___jp_5708_;
}
v___jp_5703_:
{
lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5704_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5705_, 0, v_initStackSz_5702_);
v___x_5706_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5697_, v___x_5704_, v_pos_5699_, v___x_5705_);
lean_dec_ref_known(v___x_5705_, 1);
return v___x_5706_;
}
v___jp_5708_:
{
if (v___y_5709_ == 0)
{
lean_dec_ref(v_c_5696_);
goto v___jp_5703_;
}
else
{
uint32_t v___x_5710_; uint8_t v___x_5711_; uint8_t v___x_5712_; 
v___x_5710_ = 48;
v___x_5711_ = lean_uint32_dec_eq(v_curr_5707_, v___x_5710_);
v___x_5712_ = lean_bool_not(v___x_5711_);
if (v___x_5712_ == 0)
{
lean_dec_ref(v_c_5696_);
goto v___jp_5703_;
}
else
{
lean_object* v_s_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; 
lean_dec(v_initStackSz_5702_);
v_s_5713_ = l_Lean_Parser_takeWhileFn(v___f_5701_, v_c_5696_, v_s_5697_);
v___x_5714_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5715_ = l_Lean_Parser_mkNodeToken(v___x_5714_, v_pos_5699_, v___y_5709_, v_c_5696_, v_s_5713_);
return v___x_5715_;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5720_; uint8_t v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; 
v___x_5720_ = 0;
v___x_5721_ = 1;
v___x_5722_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5723_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5724_ = l_Lean_Parser_mkAntiquot(v___x_5723_, v___x_5722_, v___x_5721_, v___x_5720_);
return v___x_5724_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5725_; lean_object* v___x_5726_; 
v___x_5725_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5726_ = l_Lean_Parser_mkAtomicInfo(v___x_5725_);
return v___x_5726_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; 
v___x_5727_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5728_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set(v___x_5729_, 1, v___x_5727_);
return v___x_5729_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5730_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5731_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5732_ = l_Lean_Parser_withAntiquot(v___x_5731_, v___x_5730_);
return v___x_5732_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5733_; 
v___x_5733_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5734_, lean_object* v_s_5735_){
_start:
{
lean_inc_ref(v_s_5735_);
return v_s_5735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5736_, lean_object* v_s_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l_Lean_Parser_skip___lam__0(v_x_5736_, v_s_5737_);
lean_dec_ref(v_s_5737_);
lean_dec_ref(v_x_5736_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5744_, lean_object* v_s_5745_, lean_object* v_f_5746_, lean_object* v_b_5747_){
_start:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; uint8_t v___x_5751_; 
v___x_5748_ = l_Lean_Syntax_getArgs(v_s_5745_);
v___x_5749_ = lean_unsigned_to_nat(0u);
v___x_5750_ = lean_array_get_size(v___x_5748_);
v___x_5751_ = lean_nat_dec_lt(v___x_5749_, v___x_5750_);
if (v___x_5751_ == 0)
{
lean_object* v_toApplicative_5752_; lean_object* v_toPure_5753_; lean_object* v___x_5754_; 
lean_dec_ref(v___x_5748_);
lean_dec(v_f_5746_);
v_toApplicative_5752_ = lean_ctor_get(v_inst_5744_, 0);
lean_inc_ref(v_toApplicative_5752_);
lean_dec_ref(v_inst_5744_);
v_toPure_5753_ = lean_ctor_get(v_toApplicative_5752_, 1);
lean_inc(v_toPure_5753_);
lean_dec_ref(v_toApplicative_5752_);
v___x_5754_ = lean_apply_2(v_toPure_5753_, lean_box(0), v_b_5747_);
return v___x_5754_;
}
else
{
lean_object* v___x_5755_; uint8_t v___x_5756_; 
v___x_5755_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5755_, 0, lean_box(0));
lean_closure_set(v___x_5755_, 1, lean_box(0));
lean_closure_set(v___x_5755_, 2, lean_box(0));
lean_closure_set(v___x_5755_, 3, v_f_5746_);
v___x_5756_ = lean_nat_dec_le(v___x_5750_, v___x_5750_);
if (v___x_5756_ == 0)
{
if (v___x_5751_ == 0)
{
lean_object* v_toApplicative_5757_; lean_object* v_toPure_5758_; lean_object* v___x_5759_; 
lean_dec_ref(v___x_5755_);
lean_dec_ref(v___x_5748_);
v_toApplicative_5757_ = lean_ctor_get(v_inst_5744_, 0);
lean_inc_ref(v_toApplicative_5757_);
lean_dec_ref(v_inst_5744_);
v_toPure_5758_ = lean_ctor_get(v_toApplicative_5757_, 1);
lean_inc(v_toPure_5758_);
lean_dec_ref(v_toApplicative_5757_);
v___x_5759_ = lean_apply_2(v_toPure_5758_, lean_box(0), v_b_5747_);
return v___x_5759_;
}
else
{
size_t v___x_5760_; size_t v___x_5761_; lean_object* v___x_5762_; 
v___x_5760_ = ((size_t)0ULL);
v___x_5761_ = lean_usize_of_nat(v___x_5750_);
v___x_5762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5744_, v___x_5755_, v___x_5748_, v___x_5760_, v___x_5761_, v_b_5747_);
return v___x_5762_;
}
}
else
{
size_t v___x_5763_; size_t v___x_5764_; lean_object* v___x_5765_; 
v___x_5763_ = ((size_t)0ULL);
v___x_5764_ = lean_usize_of_nat(v___x_5750_);
v___x_5765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5744_, v___x_5755_, v___x_5748_, v___x_5763_, v___x_5764_, v_b_5747_);
return v___x_5765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5766_, lean_object* v_s_5767_, lean_object* v_f_5768_, lean_object* v_b_5769_){
_start:
{
lean_object* v_res_5770_; 
v_res_5770_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5766_, v_s_5767_, v_f_5768_, v_b_5769_);
lean_dec(v_s_5767_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5771_, lean_object* v_inst_5772_, lean_object* v_00_u03b2_5773_, lean_object* v_s_5774_, lean_object* v_f_5775_, lean_object* v_b_5776_){
_start:
{
lean_object* v___x_5777_; 
v___x_5777_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5772_, v_s_5774_, v_f_5775_, v_b_5776_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5778_, lean_object* v_inst_5779_, lean_object* v_00_u03b2_5780_, lean_object* v_s_5781_, lean_object* v_f_5782_, lean_object* v_b_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Lean_Syntax_foldArgsM(v_m_5778_, v_inst_5779_, v_00_u03b2_5780_, v_s_5781_, v_f_5782_, v_b_5783_);
lean_dec(v_s_5781_);
return v_res_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5785_, lean_object* v_x1_5786_, lean_object* v_x2_5787_){
_start:
{
lean_object* v___x_5788_; 
v___x_5788_ = lean_apply_2(v_f_5785_, v_x1_5786_, v_x2_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5789_, lean_object* v_as_5790_, size_t v_i_5791_, size_t v_stop_5792_, lean_object* v_b_5793_){
_start:
{
uint8_t v___x_5794_; 
v___x_5794_ = lean_usize_dec_eq(v_i_5791_, v_stop_5792_);
if (v___x_5794_ == 0)
{
lean_object* v___x_5795_; lean_object* v___x_5796_; size_t v___x_5797_; size_t v___x_5798_; 
v___x_5795_ = lean_array_uget_borrowed(v_as_5790_, v_i_5791_);
lean_inc(v_f_5789_);
lean_inc(v___x_5795_);
v___x_5796_ = lean_apply_2(v_f_5789_, v___x_5795_, v_b_5793_);
v___x_5797_ = ((size_t)1ULL);
v___x_5798_ = lean_usize_add(v_i_5791_, v___x_5797_);
v_i_5791_ = v___x_5798_;
v_b_5793_ = v___x_5796_;
goto _start;
}
else
{
lean_dec(v_f_5789_);
return v_b_5793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5800_, lean_object* v_as_5801_, lean_object* v_i_5802_, lean_object* v_stop_5803_, lean_object* v_b_5804_){
_start:
{
size_t v_i_boxed_5805_; size_t v_stop_boxed_5806_; lean_object* v_res_5807_; 
v_i_boxed_5805_ = lean_unbox_usize(v_i_5802_);
lean_dec(v_i_5802_);
v_stop_boxed_5806_ = lean_unbox_usize(v_stop_5803_);
lean_dec(v_stop_5803_);
v_res_5807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5800_, v_as_5801_, v_i_boxed_5805_, v_stop_boxed_5806_, v_b_5804_);
lean_dec_ref(v_as_5801_);
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5808_, lean_object* v_f_5809_, lean_object* v_b_5810_){
_start:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; uint8_t v___x_5814_; 
v___x_5811_ = l_Lean_Syntax_getArgs(v_s_5808_);
v___x_5812_ = lean_unsigned_to_nat(0u);
v___x_5813_ = lean_array_get_size(v___x_5811_);
v___x_5814_ = lean_nat_dec_lt(v___x_5812_, v___x_5813_);
if (v___x_5814_ == 0)
{
lean_dec_ref(v___x_5811_);
lean_dec(v_f_5809_);
return v_b_5810_;
}
else
{
uint8_t v___x_5815_; 
v___x_5815_ = lean_nat_dec_le(v___x_5813_, v___x_5813_);
if (v___x_5815_ == 0)
{
if (v___x_5814_ == 0)
{
lean_dec_ref(v___x_5811_);
lean_dec(v_f_5809_);
return v_b_5810_;
}
else
{
size_t v___x_5816_; size_t v___x_5817_; lean_object* v___x_5818_; 
v___x_5816_ = ((size_t)0ULL);
v___x_5817_ = lean_usize_of_nat(v___x_5813_);
v___x_5818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5809_, v___x_5811_, v___x_5816_, v___x_5817_, v_b_5810_);
lean_dec_ref(v___x_5811_);
return v___x_5818_;
}
}
else
{
size_t v___x_5819_; size_t v___x_5820_; lean_object* v___x_5821_; 
v___x_5819_ = ((size_t)0ULL);
v___x_5820_ = lean_usize_of_nat(v___x_5813_);
v___x_5821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5809_, v___x_5811_, v___x_5819_, v___x_5820_, v_b_5810_);
lean_dec_ref(v___x_5811_);
return v___x_5821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5822_, lean_object* v_f_5823_, lean_object* v_b_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5822_, v_f_5823_, v_b_5824_);
lean_dec(v_s_5822_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5826_, lean_object* v_f_5827_, lean_object* v_b_5828_){
_start:
{
lean_object* v___f_5829_; lean_object* v___x_5830_; 
v___f_5829_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5829_, 0, v_f_5827_);
v___x_5830_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5826_, v___f_5829_, v_b_5828_);
return v___x_5830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_5831_, lean_object* v_f_5832_, lean_object* v_b_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l_Lean_Syntax_foldArgs___redArg(v_s_5831_, v_f_5832_, v_b_5833_);
lean_dec(v_s_5831_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_5835_, lean_object* v_s_5836_, lean_object* v_f_5837_, lean_object* v_b_5838_){
_start:
{
lean_object* v___x_5839_; 
v___x_5839_ = l_Lean_Syntax_foldArgs___redArg(v_s_5836_, v_f_5837_, v_b_5838_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_5840_, lean_object* v_s_5841_, lean_object* v_f_5842_, lean_object* v_b_5843_){
_start:
{
lean_object* v_res_5844_; 
v_res_5844_ = l_Lean_Syntax_foldArgs(v_00_u03b2_5840_, v_s_5841_, v_f_5842_, v_b_5843_);
lean_dec(v_s_5841_);
return v_res_5844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_5845_, lean_object* v_s_5846_, lean_object* v_f_5847_, lean_object* v_b_5848_){
_start:
{
lean_object* v___x_5849_; 
v___x_5849_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5846_, v_f_5847_, v_b_5848_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_5850_, lean_object* v_s_5851_, lean_object* v_f_5852_, lean_object* v_b_5853_){
_start:
{
lean_object* v_res_5854_; 
v_res_5854_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_5850_, v_s_5851_, v_f_5852_, v_b_5853_);
lean_dec(v_s_5851_);
return v_res_5854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_5855_, lean_object* v_f_5856_, lean_object* v_as_5857_, size_t v_i_5858_, size_t v_stop_5859_, lean_object* v_b_5860_){
_start:
{
lean_object* v___x_5861_; 
v___x_5861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5856_, v_as_5857_, v_i_5858_, v_stop_5859_, v_b_5860_);
return v___x_5861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5862_, lean_object* v_f_5863_, lean_object* v_as_5864_, lean_object* v_i_5865_, lean_object* v_stop_5866_, lean_object* v_b_5867_){
_start:
{
size_t v_i_boxed_5868_; size_t v_stop_boxed_5869_; lean_object* v_res_5870_; 
v_i_boxed_5868_ = lean_unbox_usize(v_i_5865_);
lean_dec(v_i_5865_);
v_stop_boxed_5869_ = lean_unbox_usize(v_stop_5866_);
lean_dec(v_stop_5866_);
v_res_5870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_5862_, v_f_5863_, v_as_5864_, v_i_boxed_5868_, v_stop_boxed_5869_, v_b_5867_);
lean_dec_ref(v_as_5864_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_5871_, lean_object* v_s_5872_, lean_object* v_x_5873_){
_start:
{
lean_object* v___x_5874_; 
v___x_5874_ = lean_apply_1(v_f_5871_, v_s_5872_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_5875_, lean_object* v_s_5876_, lean_object* v_f_5877_){
_start:
{
lean_object* v___f_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___f_5878_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5878_, 0, v_f_5877_);
v___x_5879_ = lean_box(0);
v___x_5880_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5875_, v_s_5876_, v___f_5878_, v___x_5879_);
return v___x_5880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_5881_, lean_object* v_s_5882_, lean_object* v_f_5883_){
_start:
{
lean_object* v_res_5884_; 
v_res_5884_ = l_Lean_Syntax_forArgsM___redArg(v_inst_5881_, v_s_5882_, v_f_5883_);
lean_dec(v_s_5882_);
return v_res_5884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_5885_, lean_object* v_inst_5886_, lean_object* v_s_5887_, lean_object* v_f_5888_){
_start:
{
lean_object* v___x_5889_; 
v___x_5889_ = l_Lean_Syntax_forArgsM___redArg(v_inst_5886_, v_s_5887_, v_f_5888_);
return v___x_5889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_5890_, lean_object* v_inst_5891_, lean_object* v_s_5892_, lean_object* v_f_5893_){
_start:
{
lean_object* v_res_5894_; 
v_res_5894_ = l_Lean_Syntax_forArgsM(v_m_5890_, v_inst_5891_, v_s_5892_, v_f_5893_);
lean_dec(v_s_5892_);
return v_res_5894_;
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
