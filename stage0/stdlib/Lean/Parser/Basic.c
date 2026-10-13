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
extern uint32_t l_Lean_idBeginEscape;
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
extern uint32_t l_Lean_idEndEscape;
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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 200, .m_capacity = 200, .m_length = 199, .m_data = "Generate an error at the position saved with the `withPosition` combinator.\nIf `delta == true`, then it reports at saved position+1.\nThis useful to make sure a parser consumed at least one character."};
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
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 321, .m_capacity = 321, .m_length = 320, .m_data = "Run `p`, falling back to `q` if `p` failed without consuming any input.\n\nNOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser\nproducing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`\nis fine as well."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 458, .m_capacity = 458, .m_length = 457, .m_data = "The `atomic(p)` parser parses `p`, returns the same result as `p` and fails iff `p` fails,\nbut if `p` fails after consuming some tokens `atomic(p)` will fail without consuming tokens.\nThis is important for the `p <|> q` combinator, because it is not backtracking, and will fail if\n`p` fails after consuming some tokens. To get backtracking behavior, use `atomic(p) <|> q` instead.\n\nThis parser has the same arity as `p` - it produces the same result as `p`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 454, .m_capacity = 454, .m_length = 453, .m_data = "Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is provided with information about the failing parser's effects , and it is run in the\nstate immediately after the failure.\n\nThe interactions between <|> and `recover'` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 380, .m_capacity = 380, .m_length = 379, .m_data = "Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is run in the state immediately after the failure.\n\nThe interactions between <|> and `recover` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 309, .m_capacity = 309, .m_length = 308, .m_data = "`lookahead(p)` runs `p` and fails if `p` does, but it produces no parse nodes and rewinds the\nposition to the original state on success. So for example `lookahead(\"=>\")` will ensure that the\nnext token is `\"=>\"`, without actually consuming this token.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 174, .m_capacity = 174, .m_length = 173, .m_data = "`notFollowedBy(p, \"foo\")` succeeds iff `p` fails;\nif `p` succeeds then it fails with the message `\"unexpected foo\"`.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 215, .m_capacity = 215, .m_length = 214, .m_data = "The `ws` parser requires that there is some whitespace at this location.\nFor example, the parser `\"foo\" ws \"+\"` parses `foo +` or `foo/- -/+` but not `foo+`.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 187, .m_capacity = 187, .m_length = 186, .m_data = "The `linebreak` parser requires that there is at least one line break at this location.\n(The line break may be inside a comment.)\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 412, .m_capacity = 412, .m_length = 411, .m_data = "The `noWs` parser requires that there is *no* whitespace between the preceding and following\nparsers. For example, the parser `\"foo\" noWs \"+\"` parses `foo+` but not `foo +`.\n\nThis is almost the same as `\"foo+\"`, but using this parser will make `foo+` a token, which may cause\nproblems for the use of `\"foo\"` and `\"+\"` as separate tokens in other parsers.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 298, .m_capacity = 298, .m_length = 297, .m_data = "The `colEq` parser ensures that the next token starts at exactly the column of the saved\nposition (see `withPosition`). This can be used to do whitespace sensitive syntax like\na `by` block or `do` block, where all the lines have to line up.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 473, .m_capacity = 473, .m_length = 472, .m_data = "The `colGe` parser requires that the next token starts from at least the column of the saved\nposition (see `withPosition`), but allows it to be more indented.\nThis can be used for whitespace sensitive syntax to ensure that a block does not go outside a\ncertain indentation scope. For example it is used in the lean grammar for `else if`, to ensure\nthat the `else` is not less indented than the `if` it matches with.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 571, .m_capacity = 571, .m_length = 570, .m_data = "The `colGt` parser requires that the next token starts a strictly greater column than the saved\nposition (see `withPosition`). This can be used for whitespace sensitive syntax for the arguments\nto a tactic, to ensure that the following tactic is not interpreted as an argument.\n```\nexample (x : False) : False := by\n  revert x\n  exact id\n```\nHere, the `revert` tactic is followed by a list of `colGt ident`, because otherwise it would\ninterpret `exact` as an identifier and try to revert a variable named `exact`.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 366, .m_capacity = 366, .m_length = 365, .m_data = "The `lineEq` parser requires that the current token is on the same line as the saved position\n(see `withPosition`). This can be used to ensure that composite tokens are not \"broken up\" across\ndifferent lines. For example, `else if` is parsed using `lineEq` to ensure that the two tokens\nare on the same line.\n\nThis parser has arity 0 - it does not capture anything."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 760, .m_capacity = 760, .m_length = 759, .m_data = "`withPosition(p)` runs `p` while setting the \"saved position\" to the current position.\nThis has no effect on its own, but various other parsers access this position to achieve some\ncomposite effect:\n\n* `colGt`, `colGe`, `colEq` compare the column of the saved position to the current position,\n  used to implement Python-style indentation sensitive blocks\n* `lineEq` ensures that the current position is still on the same line as the saved position,\n  used to implement composite tokens\n\nThe saved position is only available in the read-only state, which is why this is a scoping parser:\nafter the `withPosition(..)` block the saved position will be restored to its original value.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 330, .m_capacity = 330, .m_length = 329, .m_data = "`withoutPosition(p)` runs `p` without the saved position, meaning that position-checking\nparsers like `colGt` will have no effect. This is usually used by bracketing constructs like\n`(...)` so that the user can locally override whitespace sensitivity.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 496, .m_capacity = 496, .m_length = 495, .m_data = "`withForbidden tk p` runs `p` with `tk` as a \"forbidden token\". This means that if the token\nappears anywhere in `p` (unless it is nested in `withoutForbidden`), parsing will immediately\nstop there, making `tk` effectively a lowest-precedence operator. This is used for parsers like\n`for x in arr do ...`: `arr` is parsed as `withForbidden \"do\" term` because otherwise `arr do ...`\nwould be treated as an application.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 288, .m_capacity = 288, .m_length = 287, .m_data = "`withForbiddens(tks, p)` runs `p` with every token in `tks` treated as forbidden, i.e. the\ncombined effect of nesting `withForbidden` for each token (see `withForbidden`). The tokens in\n`tks` must be distinct.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 301, .m_capacity = 301, .m_length = 300, .m_data = "`withoutForbidden(p)` runs `p` disabling the \"forbidden token\" (see `withForbidden`), if any.\nThis is usually used by bracketing constructs like `(...)` because there is no parsing ambiguity\ninside these nested constructs.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`."};
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
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "categoryParserFnExtension"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 13, 93, 89, 143, 213, 101, 64)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__value;
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Fail if previous token is immediately followed by ':'."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 256, .m_capacity = 256, .m_length = 255, .m_data = "Define parser for `$e` (if `anonymous == true`) and `$e:name`.\n`kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.\nAntiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Optimized version of `mkAntiquot ... <|> p`."};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotAcceptLhs(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "withAntiquotAcceptLhs"};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 64, 68, 27, 164, 181, 212)}};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 283, .m_capacity = 283, .m_length = 282, .m_data = "Like `withAntiquot`, but uses `OrElseOnAntiquotBehavior.acceptLhs` instead of `.takeLongest`.\nThis means that when the antiquotation parser `antiquotP` succeeds, `p` is not tried.\nThis is useful when `p` has side effects on the parser stack that would not be undone by\nbacktracking."};
static const lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Parse `$[p]suffix`, e.g. `$[p],*`."};
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
static const lean_string_object l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node."};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(lean_object* v_x_145_, lean_object* v_x_146_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0___boxed(lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_x_153_, v_x_154_);
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
v___x_164_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_162_, v___x_163_);
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
v___x_384_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_381_, v___x_383_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl(uint8_t v_x_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(v_x_523_);
v___x_525_ = lean_obj_tag_nat(v___x_524_);
lean_dec(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl___boxed(lean_object* v_x_526_){
_start:
{
uint8_t v_x_4__boxed_527_; lean_object* v_res_528_; 
v_x_4__boxed_527_ = lean_unbox(v_x_526_);
v_res_528_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl(v_x_4__boxed_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(lean_object* v_k_529_){
_start:
{
lean_inc(v_k_529_);
return v_k_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg___boxed(lean_object* v_k_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___redArg(v_k_530_);
lean_dec(v_k_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_object* v_motive_532_, lean_object* v_ctorIdx_533_, uint8_t v_t_534_, lean_object* v_h_535_, lean_object* v_k_536_){
_start:
{
lean_inc(v_k_536_);
return v_k_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___boxed(lean_object* v_motive_537_, lean_object* v_ctorIdx_538_, lean_object* v_t_539_, lean_object* v_h_540_, lean_object* v_k_541_){
_start:
{
uint8_t v_t_boxed_542_; lean_object* v_res_543_; 
v_t_boxed_542_ = lean_unbox(v_t_539_);
v_res_543_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(v_motive_537_, v_ctorIdx_538_, v_t_boxed_542_, v_h_540_, v_k_541_);
lean_dec(v_k_541_);
lean_dec(v_ctorIdx_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(lean_object* v_acceptLhs_544_){
_start:
{
lean_inc(v_acceptLhs_544_);
return v_acceptLhs_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg___boxed(lean_object* v_acceptLhs_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(v_acceptLhs_545_);
lean_dec(v_acceptLhs_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_object* v_motive_547_, uint8_t v_t_548_, lean_object* v_h_549_, lean_object* v_acceptLhs_550_){
_start:
{
lean_inc(v_acceptLhs_550_);
return v_acceptLhs_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___boxed(lean_object* v_motive_551_, lean_object* v_t_552_, lean_object* v_h_553_, lean_object* v_acceptLhs_554_){
_start:
{
uint8_t v_t_boxed_555_; lean_object* v_res_556_; 
v_t_boxed_555_ = lean_unbox(v_t_552_);
v_res_556_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(v_motive_551_, v_t_boxed_555_, v_h_553_, v_acceptLhs_554_);
lean_dec(v_acceptLhs_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(lean_object* v_takeLongest_557_){
_start:
{
lean_inc(v_takeLongest_557_);
return v_takeLongest_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg___boxed(lean_object* v_takeLongest_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___redArg(v_takeLongest_558_);
lean_dec(v_takeLongest_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_object* v_motive_560_, uint8_t v_t_561_, lean_object* v_h_562_, lean_object* v_takeLongest_563_){
_start:
{
lean_inc(v_takeLongest_563_);
return v_takeLongest_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___boxed(lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_takeLongest_567_){
_start:
{
uint8_t v_t_boxed_568_; lean_object* v_res_569_; 
v_t_boxed_568_ = lean_unbox(v_t_565_);
v_res_569_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(v_motive_564_, v_t_boxed_568_, v_h_566_, v_takeLongest_567_);
lean_dec(v_takeLongest_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(lean_object* v_merge_570_){
_start:
{
lean_inc(v_merge_570_);
return v_merge_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg___boxed(lean_object* v_merge_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(v_merge_571_);
lean_dec(v_merge_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_object* v_motive_573_, uint8_t v_t_574_, lean_object* v_h_575_, lean_object* v_merge_576_){
_start:
{
lean_inc(v_merge_576_);
return v_merge_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___boxed(lean_object* v_motive_577_, lean_object* v_t_578_, lean_object* v_h_579_, lean_object* v_merge_580_){
_start:
{
uint8_t v_t_boxed_581_; lean_object* v_res_582_; 
v_t_boxed_581_ = lean_unbox(v_t_578_);
v_res_582_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(v_motive_577_, v_t_boxed_581_, v_h_579_, v_merge_580_);
lean_dec(v_merge_580_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(uint8_t v_x_583_, uint8_t v_y_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_585_ = lean_box(v_x_583_);
v___x_586_ = lean_obj_tag_nat(v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = lean_box(v_y_584_);
v___x_588_ = lean_obj_tag_nat(v___x_587_);
lean_dec(v___x_587_);
v___x_589_ = lean_nat_dec_eq(v___x_586_, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed(lean_object* v_x_590_, lean_object* v_y_591_){
_start:
{
uint8_t v_x_24__boxed_592_; uint8_t v_y_25__boxed_593_; uint8_t v_res_594_; lean_object* v_r_595_; 
v_x_24__boxed_592_ = lean_unbox(v_x_590_);
v_y_25__boxed_593_ = lean_unbox(v_y_591_);
v_res_594_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_24__boxed_592_, v_y_25__boxed_593_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object* v_stx_601_, lean_object* v_s_602_){
_start:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
lean_inc(v_stx_601_);
v___x_604_ = l_Lean_Syntax_isOfKind(v_stx_601_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Parser_ParserState_pushSyntax(v_s_602_, v_stx_601_);
return v___x_605_;
}
else
{
lean_object* v_stxStack_606_; lean_object* v_lhsPrec_607_; lean_object* v_pos_608_; lean_object* v_cache_609_; lean_object* v_errorMsg_610_; lean_object* v_recoveredErrors_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_629_; 
v_stxStack_606_ = lean_ctor_get(v_s_602_, 0);
v_lhsPrec_607_ = lean_ctor_get(v_s_602_, 1);
v_pos_608_ = lean_ctor_get(v_s_602_, 2);
v_cache_609_ = lean_ctor_get(v_s_602_, 3);
v_errorMsg_610_ = lean_ctor_get(v_s_602_, 4);
v_recoveredErrors_611_ = lean_ctor_get(v_s_602_, 5);
v_isSharedCheck_629_ = !lean_is_exclusive(v_s_602_);
if (v_isSharedCheck_629_ == 0)
{
v___x_613_ = v_s_602_;
v_isShared_614_ = v_isSharedCheck_629_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_recoveredErrors_611_);
lean_inc(v_errorMsg_610_);
lean_inc(v_cache_609_);
lean_inc(v_pos_608_);
lean_inc(v_lhsPrec_607_);
lean_inc(v_stxStack_606_);
lean_dec(v_s_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_629_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_raw_615_; lean_object* v_drop_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_raw_615_ = lean_ctor_get(v_stxStack_606_, 0);
v_drop_616_ = lean_ctor_get(v_stxStack_606_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_stxStack_606_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v_stxStack_606_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_drop_616_);
lean_inc(v_raw_615_);
lean_dec(v_stxStack_606_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_620_ = l_Lean_Syntax_getArgs(v_stx_601_);
lean_dec(v_stx_601_);
v___x_621_ = l_Array_append___redArg(v_raw_615_, v___x_620_);
lean_dec_ref(v___x_620_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_621_);
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_drop_616_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_623_);
v___x_625_ = v___x_613_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_lhsPrec_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_pos_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_cache_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_errorMsg_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_recoveredErrors_611_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* v_p_630_, lean_object* v_q_631_, uint8_t v_antiquotBehavior_632_, lean_object* v_c_633_, lean_object* v_s_634_){
_start:
{
lean_object* v_pos_635_; lean_object* v_iniSz_636_; lean_object* v_s_637_; lean_object* v_errorMsg_638_; 
v_pos_635_ = lean_ctor_get(v_s_634_, 2);
lean_inc(v_pos_635_);
v_iniSz_636_ = l_Lean_Parser_ParserState_stackSize(v_s_634_);
lean_inc_ref(v_c_633_);
v_s_637_ = lean_apply_2(v_p_630_, v_c_633_, v_s_634_);
v_errorMsg_638_ = lean_ctor_get(v_s_637_, 4);
lean_inc(v_errorMsg_638_);
if (lean_obj_tag(v_errorMsg_638_) == 0)
{
lean_object* v_stxStack_639_; lean_object* v_pos_640_; lean_object* v_pBack_641_; lean_object* v___y_643_; lean_object* v___y_647_; uint8_t v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_659_; uint8_t v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; uint8_t v___y_669_; uint8_t v___x_686_; uint8_t v___x_687_; 
v_stxStack_639_ = lean_ctor_get(v_s_637_, 0);
lean_inc_ref(v_stxStack_639_);
v_pos_640_ = lean_ctor_get(v_s_637_, 2);
lean_inc(v_pos_640_);
v_pBack_641_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_639_);
lean_dec_ref(v_stxStack_639_);
v___x_686_ = 0;
v___x_687_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_632_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_688_ = l_Lean_Parser_ParserState_stackSize(v_s_637_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_iniSz_636_, v___x_689_);
v___x_691_ = lean_nat_dec_eq(v___x_688_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_688_);
if (v___x_691_ == 0)
{
lean_dec(v_pBack_641_);
lean_dec(v_pos_640_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
else
{
v___y_669_ = v___x_687_;
goto v___jp_668_;
}
}
else
{
v___y_669_ = v___x_687_;
goto v___jp_668_;
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = l_Lean_Parser_ParserState_restore(v___y_643_, v_iniSz_636_, v_pos_640_);
lean_dec(v_iniSz_636_);
v___x_645_ = l_Lean_Parser_ParserState_pushSyntax(v___x_644_, v_pBack_641_);
return v___x_645_;
}
v___jp_646_:
{
if (v___y_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = l_Lean_Parser_SyntaxStack_back(v___y_647_);
lean_dec_ref(v___y_647_);
lean_inc(v___x_651_);
v___x_652_ = l_Lean_Syntax_isAntiquots(v___x_651_);
if (v___x_652_ == 0)
{
lean_dec(v___x_651_);
v___y_643_ = v___y_649_;
goto v___jp_642_;
}
else
{
if (v___y_648_ == 0)
{
lean_object* v_s_653_; lean_object* v_s_654_; lean_object* v_s_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_pos_640_);
v_s_653_ = l_Lean_Parser_ParserState_popSyntax(v___y_649_);
v_s_654_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_641_, v_s_653_);
v_s_655_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_651_, v_s_654_);
v___x_656_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_657_ = l_Lean_Parser_ParserState_mkNode(v_s_655_, v___x_656_, v_iniSz_636_);
lean_dec(v_iniSz_636_);
return v___x_657_;
}
else
{
lean_dec(v___x_651_);
v___y_643_ = v___y_649_;
goto v___jp_642_;
}
}
}
else
{
lean_dec_ref(v___y_647_);
v___y_643_ = v___y_649_;
goto v___jp_642_;
}
}
v___jp_658_:
{
if (v___y_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = l_Lean_Parser_ParserState_stackSize(v___y_662_);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_iniSz_636_, v___x_665_);
v___x_667_ = lean_nat_dec_eq(v___x_664_, v___x_666_);
lean_dec(v___x_666_);
lean_dec(v___x_664_);
if (v___x_667_ == 0)
{
v___y_647_ = v___y_659_;
v___y_648_ = v___y_660_;
v___y_649_ = v___y_662_;
v___y_650_ = v___y_661_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___y_659_;
v___y_648_ = v___y_660_;
v___y_649_ = v___y_662_;
v___y_650_ = v___y_660_;
goto v___jp_646_;
}
}
else
{
lean_dec_ref(v___y_659_);
v___y_643_ = v___y_662_;
goto v___jp_642_;
}
}
v___jp_668_:
{
if (v___y_669_ == 0)
{
uint8_t v___x_670_; 
lean_inc(v_pBack_641_);
v___x_670_ = l_Lean_Syntax_isAntiquots(v_pBack_641_);
if (v___x_670_ == 0)
{
lean_dec(v_pBack_641_);
lean_dec(v_pos_640_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
else
{
lean_object* v_s_671_; lean_object* v_s_672_; lean_object* v_stxStack_673_; lean_object* v_pos_674_; lean_object* v_errorMsg_675_; uint8_t v___x_676_; 
v_s_671_ = l_Lean_Parser_ParserState_restore(v_s_637_, v_iniSz_636_, v_pos_635_);
v_s_672_ = lean_apply_2(v_q_631_, v_c_633_, v_s_671_);
v_stxStack_673_ = lean_ctor_get(v_s_672_, 0);
lean_inc_ref(v_stxStack_673_);
v_pos_674_ = lean_ctor_get(v_s_672_, 2);
lean_inc(v_pos_674_);
v_errorMsg_675_ = lean_ctor_get(v_s_672_, 4);
lean_inc(v_errorMsg_675_);
v___x_676_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_675_, v_errorMsg_638_);
lean_dec(v_errorMsg_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_pos_674_);
lean_dec_ref(v_stxStack_673_);
v___x_677_ = l_Lean_Parser_ParserState_restore(v_s_672_, v_iniSz_636_, v_pos_640_);
lean_dec(v_iniSz_636_);
v___x_678_ = l_Lean_Parser_ParserState_pushSyntax(v___x_677_, v_pBack_641_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_pos_640_, v___x_679_);
v___x_681_ = lean_nat_dec_le(v___x_680_, v_pos_674_);
lean_dec(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_nat_add(v_pos_674_, v___x_679_);
lean_dec(v_pos_674_);
v___x_683_ = lean_nat_dec_le(v___x_682_, v_pos_640_);
lean_dec(v___x_682_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = 2;
v___x_685_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_632_, v___x_684_);
if (v___x_685_ == 0)
{
v___y_659_ = v_stxStack_673_;
v___y_660_ = v___x_681_;
v___y_661_ = v___x_676_;
v___y_662_ = v_s_672_;
v___y_663_ = v___x_676_;
goto v___jp_658_;
}
else
{
v___y_659_ = v_stxStack_673_;
v___y_660_ = v___x_681_;
v___y_661_ = v___x_676_;
v___y_662_ = v_s_672_;
v___y_663_ = v___x_681_;
goto v___jp_658_;
}
}
else
{
v___y_659_ = v_stxStack_673_;
v___y_660_ = v___x_681_;
v___y_661_ = v___x_676_;
v___y_662_ = v_s_672_;
v___y_663_ = v___x_683_;
goto v___jp_658_;
}
}
else
{
lean_dec(v_pos_674_);
lean_dec_ref(v_stxStack_673_);
lean_dec(v_pBack_641_);
lean_dec(v_pos_640_);
lean_dec(v_iniSz_636_);
return v_s_672_;
}
}
}
}
else
{
lean_dec(v_pBack_641_);
lean_dec(v_pos_640_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
}
}
else
{
lean_object* v_pos_692_; lean_object* v_val_693_; uint8_t v_decide_694_; 
v_pos_692_ = lean_ctor_get(v_s_637_, 2);
lean_inc(v_pos_692_);
v_val_693_ = lean_ctor_get(v_errorMsg_638_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v_errorMsg_638_, 1);
v_decide_694_ = lean_nat_dec_eq(v_pos_692_, v_pos_635_);
lean_dec(v_pos_692_);
if (v_decide_694_ == 0)
{
lean_dec(v_val_693_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc(v_pos_635_);
v___x_695_ = l_Lean_Parser_ParserState_restore(v_s_637_, v_iniSz_636_, v_pos_635_);
lean_dec(v_iniSz_636_);
v___x_696_ = lean_apply_2(v_q_631_, v_c_633_, v___x_695_);
v___x_697_ = l_Lean_Parser_mergeOrElseErrors(v___x_696_, v_val_693_, v_pos_635_, v_decide_694_);
lean_dec(v_pos_635_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_698_, lean_object* v_q_699_, lean_object* v_antiquotBehavior_700_, lean_object* v_c_701_, lean_object* v_s_702_){
_start:
{
uint8_t v_antiquotBehavior_boxed_703_; lean_object* v_res_704_; 
v_antiquotBehavior_boxed_703_ = lean_unbox(v_antiquotBehavior_700_);
v_res_704_ = l_Lean_Parser_orelseFnCore(v_p_698_, v_q_699_, v_antiquotBehavior_boxed_703_, v_c_701_, v_s_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_705_, lean_object* v_q_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
uint8_t v___x_709_; lean_object* v___x_710_; 
v___x_709_ = 2;
v___x_710_ = l_Lean_Parser_orelseFnCore(v_p_705_, v_q_706_, v___x_709_, v_a_707_, v_a_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_711_, lean_object* v_q_712_){
_start:
{
lean_object* v_collectTokens_713_; lean_object* v_collectKinds_714_; lean_object* v_firstTokens_715_; lean_object* v_collectTokens_716_; lean_object* v_collectKinds_717_; lean_object* v_firstTokens_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_728_; 
v_collectTokens_713_ = lean_ctor_get(v_p_711_, 0);
lean_inc_ref(v_collectTokens_713_);
v_collectKinds_714_ = lean_ctor_get(v_p_711_, 1);
lean_inc_ref(v_collectKinds_714_);
v_firstTokens_715_ = lean_ctor_get(v_p_711_, 2);
lean_inc(v_firstTokens_715_);
lean_dec_ref(v_p_711_);
v_collectTokens_716_ = lean_ctor_get(v_q_712_, 0);
v_collectKinds_717_ = lean_ctor_get(v_q_712_, 1);
v_firstTokens_718_ = lean_ctor_get(v_q_712_, 2);
v_isSharedCheck_728_ = !lean_is_exclusive(v_q_712_);
if (v_isSharedCheck_728_ == 0)
{
v___x_720_ = v_q_712_;
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_firstTokens_718_);
lean_inc(v_collectKinds_717_);
lean_inc(v_collectTokens_716_);
lean_dec(v_q_712_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___f_722_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_722_, 0, v_collectKinds_717_);
lean_closure_set(v___f_722_, 1, v_collectKinds_714_);
v___f_723_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_723_, 0, v_collectTokens_716_);
lean_closure_set(v___f_723_, 1, v_collectTokens_713_);
v___x_724_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_715_, v_firstTokens_718_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 2, v___x_724_);
lean_ctor_set(v___x_720_, 1, v___f_722_);
lean_ctor_set(v___x_720_, 0, v___f_723_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___f_723_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___f_722_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_729_, lean_object* v_p2_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_box(0);
v___x_734_ = lean_apply_1(v_p2_730_, v___x_733_);
v___x_735_ = l_Lean_Parser_orelseFn(v_p1_729_, v___x_734_, v___y_731_, v___y_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_738_, lean_object* v_q_739_){
_start:
{
lean_object* v_info_740_; lean_object* v_fn_741_; lean_object* v_info_742_; lean_object* v_fn_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_752_; 
v_info_740_ = lean_ctor_get(v_p_738_, 0);
lean_inc_ref(v_info_740_);
v_fn_741_ = lean_ctor_get(v_p_738_, 1);
lean_inc_ref(v_fn_741_);
lean_dec_ref(v_p_738_);
v_info_742_ = lean_ctor_get(v_q_739_, 0);
v_fn_743_ = lean_ctor_get(v_q_739_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_q_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_745_ = v_q_739_;
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_fn_743_);
lean_inc(v_info_742_);
lean_dec(v_q_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = l_Lean_Parser_orelseInfo(v_info_740_, v_info_742_);
v___x_748_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_748_, 0, v_fn_741_);
lean_closure_set(v___x_748_, 1, v_fn_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_748_);
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_761_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_762_ = l_Lean_addBuiltinDocString(v___x_760_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_box(0);
v___x_768_ = lean_apply_1(v_b_766_, v___x_767_);
v___x_769_ = l_Lean_Parser_orelse(v_a_765_, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_772_){
_start:
{
lean_object* v_collectTokens_773_; lean_object* v_collectKinds_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_collectTokens_773_ = lean_ctor_get(v_info_772_, 0);
v_collectKinds_774_ = lean_ctor_get(v_info_772_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_info_772_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v_info_772_, 2);
lean_dec(v_unused_783_);
v___x_776_ = v_info_772_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_collectKinds_774_);
lean_inc(v_collectTokens_773_);
lean_dec(v_info_772_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_box(1);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_collectTokens_773_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_collectKinds_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_784_, lean_object* v_c_785_, lean_object* v_s_786_){
_start:
{
lean_object* v_pos_787_; lean_object* v___x_788_; lean_object* v_errorMsg_789_; 
v_pos_787_ = lean_ctor_get(v_s_786_, 2);
lean_inc(v_pos_787_);
v___x_788_ = lean_apply_2(v_p_784_, v_c_785_, v_s_786_);
v_errorMsg_789_ = lean_ctor_get(v___x_788_, 4);
lean_inc(v_errorMsg_789_);
if (lean_obj_tag(v_errorMsg_789_) == 1)
{
lean_object* v_stxStack_790_; lean_object* v_lhsPrec_791_; lean_object* v_cache_792_; lean_object* v_recoveredErrors_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_stxStack_790_ = lean_ctor_get(v___x_788_, 0);
v_lhsPrec_791_ = lean_ctor_get(v___x_788_, 1);
v_cache_792_ = lean_ctor_get(v___x_788_, 3);
v_recoveredErrors_793_ = lean_ctor_get(v___x_788_, 5);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_801_ = lean_ctor_get(v___x_788_, 4);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v___x_788_, 2);
lean_dec(v_unused_802_);
v___x_795_ = v___x_788_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_recoveredErrors_793_);
lean_inc(v_cache_792_);
lean_inc(v_lhsPrec_791_);
lean_inc(v_stxStack_790_);
lean_dec(v___x_788_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 2, v_pos_787_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_stxStack_790_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_lhsPrec_791_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_pos_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_cache_792_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_errorMsg_789_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v_recoveredErrors_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_dec(v_errorMsg_789_);
lean_dec(v_pos_787_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_803_){
_start:
{
lean_object* v_info_804_; lean_object* v_fn_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_info_804_ = lean_ctor_get(v_p_803_, 0);
v_fn_805_ = lean_ctor_get(v_p_803_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_p_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v_p_803_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_fn_805_);
lean_inc(v_info_804_);
lean_dec(v_p_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_809_, 0, v_fn_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_info_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_822_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_823_ = l_Lean_addBuiltinDocString(v___x_821_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_825_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_initialPos_828_; lean_object* v_initialSize_829_; lean_object* v_initialPos_830_; lean_object* v_initialSize_831_; uint8_t v_decide_832_; 
v_initialPos_828_ = lean_ctor_get(v_x_826_, 0);
v_initialSize_829_ = lean_ctor_get(v_x_826_, 1);
v_initialPos_830_ = lean_ctor_get(v_x_827_, 0);
v_initialSize_831_ = lean_ctor_get(v_x_827_, 1);
v_decide_832_ = lean_nat_dec_eq(v_initialPos_828_, v_initialPos_830_);
if (v_decide_832_ == 0)
{
return v_decide_832_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_eq(v_initialSize_829_, v_initialSize_831_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_834_, v_x_835_);
lean_dec_ref(v_x_835_);
lean_dec_ref(v_x_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_initialPos_842_; lean_object* v_initialSize_843_; lean_object* v_initialPos_844_; lean_object* v_initialSize_845_; uint8_t v_decide_846_; 
v_initialPos_842_ = lean_ctor_get(v_x_840_, 0);
v_initialSize_843_ = lean_ctor_get(v_x_840_, 1);
v_initialPos_844_ = lean_ctor_get(v_x_841_, 0);
v_initialSize_845_ = lean_ctor_get(v_x_841_, 1);
v_decide_846_ = lean_nat_dec_eq(v_initialPos_842_, v_initialPos_844_);
if (v_decide_846_ == 0)
{
return v_decide_846_;
}
else
{
uint8_t v___x_847_; 
v___x_847_ = lean_nat_dec_eq(v_initialSize_843_, v_initialSize_845_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_848_, v_x_849_);
lean_dec_ref(v_x_849_);
lean_dec_ref(v_x_848_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_855_, v_x_856_);
lean_dec_ref(v_x_856_);
lean_dec_ref(v_x_855_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(14u);
v___x_873_ = lean_nat_to_int(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_unsigned_to_nat(15u);
v___x_887_ = lean_nat_to_int(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_889_ = lean_string_length(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_891_ = lean_nat_to_int(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_894_){
_start:
{
lean_object* v_initialPos_895_; lean_object* v_initialSize_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_934_; 
v_initialPos_895_ = lean_ctor_get(v_x_894_, 0);
v_initialSize_896_ = lean_ctor_get(v_x_894_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_934_ == 0)
{
v___x_898_ = v_x_894_;
v_isShared_899_ = v_isSharedCheck_934_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_initialSize_896_);
lean_inc(v_initialPos_895_);
lean_dec(v_x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_934_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_900_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_901_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_902_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_903_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_904_ = l_Nat_reprFast(v_initialPos_895_);
v___x_905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 5);
lean_ctor_set(v___x_898_, 1, v___x_905_);
lean_ctor_set(v___x_898_, 0, v___x_903_);
v___x_907_ = v___x_898_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_905_);
v___x_907_ = v_reuseFailAlloc_933_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_908_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_902_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = 0;
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_911_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_901_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_box(1);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_900_);
v___x_921_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_922_ = l_Nat_reprFast(v_initialSize_896_);
v___x_923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___x_924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_921_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*1, v___x_911_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_920_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_928_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_926_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_908_);
v___x_931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_927_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_911_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_935_, lean_object* v_prec_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_938_, lean_object* v_prec_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_938_, v_prec_939_);
lean_dec(v_prec_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_943_, lean_object* v_recover_944_, lean_object* v_c_945_, lean_object* v_s_946_){
_start:
{
lean_object* v_stxStack_947_; lean_object* v_pos_948_; lean_object* v_s_949_; lean_object* v_errorMsg_950_; 
v_stxStack_947_ = lean_ctor_get(v_s_946_, 0);
lean_inc_ref(v_stxStack_947_);
v_pos_948_ = lean_ctor_get(v_s_946_, 2);
lean_inc(v_pos_948_);
lean_inc_ref(v_c_945_);
v_s_949_ = lean_apply_2(v_p_943_, v_c_945_, v_s_946_);
v_errorMsg_950_ = lean_ctor_get(v_s_949_, 4);
lean_inc(v_errorMsg_950_);
if (lean_obj_tag(v_errorMsg_950_) == 1)
{
lean_object* v_stxStack_951_; lean_object* v_lhsPrec_952_; lean_object* v_pos_953_; lean_object* v_cache_954_; lean_object* v_recoveredErrors_955_; lean_object* v_val_956_; lean_object* v_iniSz_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_s_x27_961_; lean_object* v_stxStack_962_; lean_object* v_pos_963_; lean_object* v_errorMsg_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_975_; 
v_stxStack_951_ = lean_ctor_get(v_s_949_, 0);
lean_inc_ref(v_stxStack_951_);
v_lhsPrec_952_ = lean_ctor_get(v_s_949_, 1);
lean_inc_n(v_lhsPrec_952_, 2);
v_pos_953_ = lean_ctor_get(v_s_949_, 2);
lean_inc(v_pos_953_);
v_cache_954_ = lean_ctor_get(v_s_949_, 3);
lean_inc_ref_n(v_cache_954_, 2);
v_recoveredErrors_955_ = lean_ctor_get(v_s_949_, 5);
lean_inc_ref_n(v_recoveredErrors_955_, 2);
v_val_956_ = lean_ctor_get(v_errorMsg_950_, 0);
lean_inc(v_val_956_);
lean_dec_ref_known(v_errorMsg_950_, 1);
v_iniSz_957_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_947_);
lean_dec_ref(v_stxStack_947_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_pos_948_);
lean_ctor_set(v___x_958_, 1, v_iniSz_957_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_960_, 0, v_stxStack_951_);
lean_ctor_set(v___x_960_, 1, v_lhsPrec_952_);
lean_ctor_set(v___x_960_, 2, v_pos_953_);
lean_ctor_set(v___x_960_, 3, v_cache_954_);
lean_ctor_set(v___x_960_, 4, v___x_959_);
lean_ctor_set(v___x_960_, 5, v_recoveredErrors_955_);
v_s_x27_961_ = lean_apply_3(v_recover_944_, v___x_958_, v_c_945_, v___x_960_);
v_stxStack_962_ = lean_ctor_get(v_s_x27_961_, 0);
v_pos_963_ = lean_ctor_get(v_s_x27_961_, 2);
v_errorMsg_964_ = lean_ctor_get(v_s_x27_961_, 4);
v_isSharedCheck_975_ = !lean_is_exclusive(v_s_x27_961_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; lean_object* v_unused_977_; lean_object* v_unused_978_; 
v_unused_976_ = lean_ctor_get(v_s_x27_961_, 5);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_s_x27_961_, 3);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_s_x27_961_, 1);
lean_dec(v_unused_978_);
v___x_966_ = v_s_x27_961_;
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_errorMsg_964_);
lean_inc(v_pos_963_);
lean_inc(v_stxStack_962_);
lean_dec(v_s_x27_961_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; 
v___x_968_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_964_, v___x_959_);
lean_dec(v_errorMsg_964_);
if (v___x_968_ == 0)
{
lean_del_object(v___x_966_);
lean_dec(v_pos_963_);
lean_dec_ref(v_stxStack_962_);
lean_dec(v_val_956_);
lean_dec_ref(v_recoveredErrors_955_);
lean_dec_ref(v_cache_954_);
lean_dec(v_lhsPrec_952_);
return v_s_949_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec_ref(v_s_949_);
lean_inc_ref(v_stxStack_962_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_stxStack_962_);
lean_ctor_set(v___x_969_, 1, v_val_956_);
lean_inc(v_pos_963_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_pos_963_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_array_push(v_recoveredErrors_955_, v___x_970_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 5, v___x_971_);
lean_ctor_set(v___x_966_, 4, v___x_959_);
lean_ctor_set(v___x_966_, 3, v_cache_954_);
lean_ctor_set(v___x_966_, 1, v_lhsPrec_952_);
v___x_973_ = v___x_966_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_stxStack_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_lhsPrec_952_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_pos_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_cache_954_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 5, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_dec(v_errorMsg_950_);
lean_dec(v_pos_948_);
lean_dec_ref(v_stxStack_947_);
lean_dec_ref(v_c_945_);
lean_dec_ref(v_recover_944_);
return v_s_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_979_, lean_object* v_s_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_983_; lean_object* v_fn_984_; lean_object* v___x_985_; 
v___x_983_ = lean_apply_1(v_handler_979_, v_s_980_);
v_fn_984_ = lean_ctor_get(v___x_983_, 1);
lean_inc_ref(v_fn_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = lean_apply_2(v_fn_984_, v___y_981_, v___y_982_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_986_, lean_object* v_handler_987_){
_start:
{
lean_object* v_info_988_; lean_object* v_fn_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v_info_988_ = lean_ctor_get(v_parser_986_, 0);
v_fn_989_ = lean_ctor_get(v_parser_986_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_parser_986_);
if (v_isSharedCheck_998_ == 0)
{
v___x_991_ = v_parser_986_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_fn_989_);
lean_inc(v_info_988_);
lean_dec(v_parser_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___f_993_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_993_, 0, v_handler_987_);
v___x_994_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_994_, 0, v_fn_989_);
lean_closure_set(v___x_994_, 1, v___f_993_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_info_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_1007_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_1008_ = l_Lean_addBuiltinDocString(v___x_1006_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_1011_, lean_object* v_x_1012_){
_start:
{
lean_inc_ref(v_handler_1011_);
return v_handler_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Parser_recover___lam__0(v_handler_1013_, v_x_1014_);
lean_dec_ref(v_x_1014_);
lean_dec_ref(v_handler_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1016_, lean_object* v_handler_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; 
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1018_, 0, v_handler_1017_);
v___x_1019_ = l_Lean_Parser_recover_x27(v_parser_1016_, v___f_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1028_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1029_ = l_Lean_addBuiltinDocString(v___x_1027_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1035_, lean_object* v_c_1036_, lean_object* v_s_1037_){
_start:
{
lean_object* v_pos_1038_; lean_object* v_iniSz_1039_; lean_object* v___y_1041_; lean_object* v_s_1044_; lean_object* v_pos_1045_; lean_object* v_errorMsg_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_pos_1038_ = lean_ctor_get(v_s_1037_, 2);
lean_inc(v_pos_1038_);
v_iniSz_1039_ = l_Lean_Parser_ParserState_stackSize(v_s_1037_);
v_s_1044_ = lean_apply_2(v_p_1035_, v_c_1036_, v_s_1037_);
v_pos_1045_ = lean_ctor_get(v_s_1044_, 2);
lean_inc(v_pos_1045_);
v_errorMsg_1046_ = lean_ctor_get(v_s_1044_, 4);
lean_inc(v_errorMsg_1046_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1046_, v___x_1047_);
lean_dec(v_errorMsg_1046_);
if (v___x_1048_ == 0)
{
uint8_t v_decide_1049_; 
v_decide_1049_ = lean_nat_dec_eq(v_pos_1045_, v_pos_1038_);
lean_dec(v_pos_1045_);
if (v_decide_1049_ == 0)
{
lean_dec(v_pos_1038_);
v___y_1041_ = v_s_1044_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Parser_ParserState_restore(v_s_1044_, v_iniSz_1039_, v_pos_1038_);
v___y_1041_ = v___x_1050_;
goto v___jp_1040_;
}
}
else
{
lean_dec(v_pos_1045_);
lean_dec(v_pos_1038_);
v___y_1041_ = v_s_1044_;
goto v___jp_1040_;
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1043_ = l_Lean_Parser_ParserState_mkNode(v___y_1041_, v___x_1042_, v_iniSz_1039_);
lean_dec(v_iniSz_1039_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1051_){
_start:
{
lean_object* v_collectTokens_1052_; lean_object* v_collectKinds_1053_; lean_object* v_firstTokens_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1062_; 
v_collectTokens_1052_ = lean_ctor_get(v_p_1051_, 0);
v_collectKinds_1053_ = lean_ctor_get(v_p_1051_, 1);
v_firstTokens_1054_ = lean_ctor_get(v_p_1051_, 2);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_p_1051_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1056_ = v_p_1051_;
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_firstTokens_1054_);
lean_inc(v_collectKinds_1053_);
lean_inc(v_collectTokens_1052_);
lean_dec(v_p_1051_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 2, v___x_1058_);
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_collectTokens_1052_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_collectKinds_1053_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1063_){
_start:
{
lean_object* v_info_1064_; lean_object* v_fn_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1074_; 
v_info_1064_ = lean_ctor_get(v_p_1063_, 0);
v_fn_1065_ = lean_ctor_get(v_p_1063_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_p_1063_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1067_ = v_p_1063_;
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_fn_1065_);
lean_inc(v_info_1064_);
lean_dec(v_p_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1069_ = l_Lean_Parser_optionalInfo(v_info_1064_);
v___x_1070_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1070_, 0, v_fn_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v___x_1070_);
lean_ctor_set(v___x_1067_, 0, v___x_1069_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1075_, lean_object* v_c_1076_, lean_object* v_s_1077_){
_start:
{
lean_object* v_pos_1078_; lean_object* v_iniSz_1079_; lean_object* v_s_1080_; lean_object* v_errorMsg_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_pos_1078_ = lean_ctor_get(v_s_1077_, 2);
lean_inc(v_pos_1078_);
v_iniSz_1079_ = l_Lean_Parser_ParserState_stackSize(v_s_1077_);
v_s_1080_ = lean_apply_2(v_p_1075_, v_c_1076_, v_s_1077_);
v_errorMsg_1081_ = lean_ctor_get(v_s_1080_, 4);
lean_inc(v_errorMsg_1081_);
v___x_1082_ = lean_box(0);
v___x_1083_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1081_, v___x_1082_);
lean_dec(v_errorMsg_1081_);
if (v___x_1083_ == 0)
{
lean_dec(v_iniSz_1079_);
lean_dec(v_pos_1078_);
return v_s_1080_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Parser_ParserState_restore(v_s_1080_, v_iniSz_1079_, v_pos_1078_);
lean_dec(v_iniSz_1079_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1085_){
_start:
{
lean_object* v_info_1086_; lean_object* v_fn_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_info_1086_ = lean_ctor_get(v_p_1085_, 0);
v_fn_1087_ = lean_ctor_get(v_p_1085_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_p_1085_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1089_ = v_p_1085_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_fn_1087_);
lean_inc(v_info_1086_);
lean_dec(v_p_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1091_, 0, v_fn_1087_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_info_1086_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1104_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1105_ = l_Lean_addBuiltinDocString(v___x_1103_, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1109_, lean_object* v_msg_1110_, lean_object* v_c_1111_, lean_object* v_s_1112_){
_start:
{
lean_object* v_pos_1113_; lean_object* v_iniSz_1114_; lean_object* v_s_1115_; lean_object* v_errorMsg_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_pos_1113_ = lean_ctor_get(v_s_1112_, 2);
lean_inc(v_pos_1113_);
v_iniSz_1114_ = l_Lean_Parser_ParserState_stackSize(v_s_1112_);
v_s_1115_ = lean_apply_2(v_p_1109_, v_c_1111_, v_s_1112_);
v_errorMsg_1116_ = lean_ctor_get(v_s_1115_, 4);
lean_inc(v_errorMsg_1116_);
v___x_1117_ = lean_box(0);
v___x_1118_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1116_, v___x_1117_);
lean_dec(v_errorMsg_1116_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Parser_ParserState_restore(v_s_1115_, v_iniSz_1114_, v_pos_1113_);
lean_dec(v_iniSz_1114_);
return v___x_1119_;
}
else
{
lean_object* v_s_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_s_1120_ = l_Lean_Parser_ParserState_restore(v_s_1115_, v_iniSz_1114_, v_pos_1113_);
lean_dec(v_iniSz_1114_);
v___x_1121_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1122_ = lean_string_append(v___x_1121_, v_msg_1110_);
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1120_, v___x_1122_, v___x_1123_, v___x_1118_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1125_, lean_object* v_msg_1126_, lean_object* v_c_1127_, lean_object* v_s_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Parser_notFollowedByFn(v_p_1125_, v_msg_1126_, v_c_1127_, v_s_1128_);
lean_dec_ref(v_msg_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1130_, lean_object* v_msg_1131_){
_start:
{
lean_object* v_fn_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1141_; 
v_fn_1132_ = lean_ctor_get(v_p_1130_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_p_1130_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v_p_1130_, 0);
lean_dec(v_unused_1142_);
v___x_1134_ = v_p_1130_;
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_fn_1132_);
lean_dec(v_p_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1137_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1137_, 0, v_fn_1132_);
lean_closure_set(v___x_1137_, 1, v_msg_1131_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1137_);
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1151_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1152_ = l_Lean_addBuiltinDocString(v___x_1150_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1156_, lean_object* v_c_1157_, lean_object* v_s_1158_){
_start:
{
lean_object* v_pos_1159_; lean_object* v_iniSz_1160_; lean_object* v_s_1161_; lean_object* v_pos_1162_; lean_object* v_errorMsg_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_pos_1159_ = lean_ctor_get(v_s_1158_, 2);
lean_inc(v_pos_1159_);
v_iniSz_1160_ = l_Lean_Parser_ParserState_stackSize(v_s_1158_);
lean_inc_ref(v_p_1156_);
lean_inc_ref(v_c_1157_);
v_s_1161_ = lean_apply_2(v_p_1156_, v_c_1157_, v_s_1158_);
v_pos_1162_ = lean_ctor_get(v_s_1161_, 2);
lean_inc(v_pos_1162_);
v_errorMsg_1163_ = lean_ctor_get(v_s_1161_, 4);
lean_inc(v_errorMsg_1163_);
v___x_1164_ = lean_box(0);
v___x_1165_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1163_, v___x_1164_);
lean_dec(v_errorMsg_1163_);
if (v___x_1165_ == 0)
{
uint8_t v_decide_1166_; 
lean_dec_ref(v_c_1157_);
lean_dec_ref(v_p_1156_);
v_decide_1166_ = lean_nat_dec_eq(v_pos_1159_, v_pos_1162_);
lean_dec(v_pos_1162_);
if (v_decide_1166_ == 0)
{
lean_dec(v_iniSz_1160_);
lean_dec(v_pos_1159_);
return v_s_1161_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Parser_ParserState_restore(v_s_1161_, v_iniSz_1160_, v_pos_1159_);
lean_dec(v_iniSz_1160_);
return v___x_1167_;
}
}
else
{
uint8_t v_decide_1168_; 
v_decide_1168_ = lean_nat_dec_eq(v_pos_1159_, v_pos_1162_);
lean_dec(v_pos_1162_);
lean_dec(v_pos_1159_);
if (v_decide_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1169_ = lean_unsigned_to_nat(1u);
v___x_1170_ = lean_nat_add(v_iniSz_1160_, v___x_1169_);
v___x_1171_ = l_Lean_Parser_ParserState_stackSize(v_s_1161_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1170_);
if (v___x_1172_ == 0)
{
lean_dec(v_iniSz_1160_);
v_s_1158_ = v_s_1161_;
goto _start;
}
else
{
lean_object* v___x_1174_; lean_object* v_s_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1175_ = l_Lean_Parser_ParserState_mkNode(v_s_1161_, v___x_1174_, v_iniSz_1160_);
lean_dec(v_iniSz_1160_);
v_s_1158_ = v_s_1175_;
goto _start;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_iniSz_1160_);
lean_dec_ref(v_c_1157_);
lean_dec_ref(v_p_1156_);
v___x_1177_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1178_ = lean_box(0);
v___x_1179_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1161_, v___x_1177_, v___x_1178_, v___x_1165_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1180_, lean_object* v_c_1181_, lean_object* v_s_1182_){
_start:
{
lean_object* v_iniSz_1183_; lean_object* v_s_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_iniSz_1183_ = l_Lean_Parser_ParserState_stackSize(v_s_1182_);
v_s_1184_ = l_Lean_Parser_manyAux(v_p_1180_, v_c_1181_, v_s_1182_);
v___x_1185_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1186_ = l_Lean_Parser_ParserState_mkNode(v_s_1184_, v___x_1185_, v_iniSz_1183_);
lean_dec(v_iniSz_1183_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1187_){
_start:
{
lean_object* v_info_1188_; lean_object* v_fn_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1198_; 
v_info_1188_ = lean_ctor_get(v_p_1187_, 0);
v_fn_1189_ = lean_ctor_get(v_p_1187_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_p_1187_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1191_ = v_p_1187_;
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_fn_1189_);
lean_inc(v_info_1188_);
lean_dec(v_p_1187_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = l_Lean_Parser_noFirstTokenInfo(v_info_1188_);
v___x_1194_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1194_, 0, v_fn_1189_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1194_);
lean_ctor_set(v___x_1191_, 0, v___x_1193_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1199_, lean_object* v_c_1200_, lean_object* v_s_1201_){
_start:
{
lean_object* v_iniSz_1202_; lean_object* v___x_1203_; lean_object* v_s_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_iniSz_1202_ = l_Lean_Parser_ParserState_stackSize(v_s_1201_);
lean_inc_ref(v_p_1199_);
v___x_1203_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1203_, 0, v_p_1199_);
v_s_1204_ = l_Lean_Parser_andthenFn(v_p_1199_, v___x_1203_, v_c_1200_, v_s_1201_);
v___x_1205_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1206_ = l_Lean_Parser_ParserState_mkNode(v_s_1204_, v___x_1205_, v_iniSz_1202_);
lean_dec(v_iniSz_1202_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1207_){
_start:
{
lean_object* v_info_1208_; lean_object* v_fn_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_info_1208_ = lean_ctor_get(v_p_1207_, 0);
v_fn_1209_ = lean_ctor_get(v_p_1207_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_p_1207_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v_p_1207_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_fn_1209_);
lean_inc(v_info_1208_);
lean_dec(v_p_1207_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1213_, 0, v_fn_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_info_1208_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1218_, lean_object* v_sep_1219_, uint8_t v_allowTrailingSep_1220_, lean_object* v_iniSz_1221_, uint8_t v_pOpt_1222_, lean_object* v_c_1223_, lean_object* v_s_1224_){
_start:
{
lean_object* v_s_1226_; lean_object* v_pos_1227_; lean_object* v_pos_1244_; lean_object* v_sz_1245_; lean_object* v_s_1246_; lean_object* v_pos_1247_; lean_object* v_errorMsg_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_pos_1244_ = lean_ctor_get(v_s_1224_, 2);
lean_inc(v_pos_1244_);
v_sz_1245_ = l_Lean_Parser_ParserState_stackSize(v_s_1224_);
lean_inc_ref(v_p_1218_);
lean_inc_ref(v_c_1223_);
v_s_1246_ = lean_apply_2(v_p_1218_, v_c_1223_, v_s_1224_);
v_pos_1247_ = lean_ctor_get(v_s_1246_, 2);
lean_inc(v_pos_1247_);
v_errorMsg_1248_ = lean_ctor_get(v_s_1246_, 4);
lean_inc(v_errorMsg_1248_);
v___x_1249_ = lean_box(0);
v___x_1250_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1248_, v___x_1249_);
lean_dec(v_errorMsg_1248_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
lean_dec_ref(v_c_1223_);
lean_dec_ref(v_sep_1219_);
lean_dec_ref(v_p_1218_);
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_add(v_pos_1244_, v___x_1251_);
v___x_1253_ = lean_nat_dec_le(v___x_1252_, v_pos_1247_);
lean_dec(v_pos_1247_);
lean_dec(v___x_1252_);
if (v___x_1253_ == 0)
{
if (v_pOpt_1222_ == 0)
{
lean_object* v___x_1254_; lean_object* v_s_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec(v_sz_1245_);
lean_dec(v_pos_1244_);
v___x_1254_ = lean_box(0);
v_s_1255_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1246_, v___x_1254_);
v___x_1256_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1257_ = l_Lean_Parser_ParserState_mkNode(v_s_1255_, v___x_1256_, v_iniSz_1221_);
return v___x_1257_;
}
else
{
lean_object* v_s_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_s_1258_ = l_Lean_Parser_ParserState_restore(v_s_1246_, v_sz_1245_, v_pos_1244_);
lean_dec(v_sz_1245_);
v___x_1259_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1260_ = l_Lean_Parser_ParserState_mkNode(v_s_1258_, v___x_1259_, v_iniSz_1221_);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_sz_1245_);
lean_dec(v_pos_1244_);
v___x_1261_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1262_ = l_Lean_Parser_ParserState_mkNode(v_s_1246_, v___x_1261_, v_iniSz_1221_);
return v___x_1262_;
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
lean_dec(v_pos_1244_);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_add(v_sz_1245_, v___x_1263_);
v___x_1265_ = l_Lean_Parser_ParserState_stackSize(v_s_1246_);
v___x_1266_ = lean_nat_dec_lt(v___x_1264_, v___x_1265_);
lean_dec(v___x_1265_);
lean_dec(v___x_1264_);
if (v___x_1266_ == 0)
{
lean_dec(v_sz_1245_);
v_s_1226_ = v_s_1246_;
v_pos_1227_ = v_pos_1247_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1267_; lean_object* v_s_1268_; lean_object* v_pos_1269_; 
lean_dec(v_pos_1247_);
v___x_1267_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1268_ = l_Lean_Parser_ParserState_mkNode(v_s_1246_, v___x_1267_, v_sz_1245_);
lean_dec(v_sz_1245_);
v_pos_1269_ = lean_ctor_get(v_s_1268_, 2);
lean_inc(v_pos_1269_);
v_s_1226_ = v_s_1268_;
v_pos_1227_ = v_pos_1269_;
goto v___jp_1225_;
}
}
v___jp_1225_:
{
lean_object* v_sz_1228_; lean_object* v_s_1229_; lean_object* v_errorMsg_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_sz_1228_ = l_Lean_Parser_ParserState_stackSize(v_s_1226_);
lean_inc_ref(v_sep_1219_);
lean_inc_ref(v_c_1223_);
v_s_1229_ = lean_apply_2(v_sep_1219_, v_c_1223_, v_s_1226_);
v_errorMsg_1230_ = lean_ctor_get(v_s_1229_, 4);
lean_inc(v_errorMsg_1230_);
v___x_1231_ = lean_box(0);
v___x_1232_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1230_, v___x_1231_);
lean_dec(v_errorMsg_1230_);
if (v___x_1232_ == 0)
{
lean_object* v_s_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v_c_1223_);
lean_dec_ref(v_sep_1219_);
lean_dec_ref(v_p_1218_);
v_s_1233_ = l_Lean_Parser_ParserState_restore(v_s_1229_, v_sz_1228_, v_pos_1227_);
lean_dec(v_sz_1228_);
v___x_1234_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1235_ = l_Lean_Parser_ParserState_mkNode(v_s_1233_, v___x_1234_, v_iniSz_1221_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
lean_dec(v_pos_1227_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_add(v_sz_1228_, v___x_1236_);
v___x_1238_ = l_Lean_Parser_ParserState_stackSize(v_s_1229_);
v___x_1239_ = lean_nat_dec_lt(v___x_1237_, v___x_1238_);
lean_dec(v___x_1238_);
lean_dec(v___x_1237_);
if (v___x_1239_ == 0)
{
lean_dec(v_sz_1228_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1220_;
lean_object* _tmp_6 = v_s_1229_;
v_pOpt_1222_ = _tmp_4;
v_s_1224_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1241_; lean_object* v_s_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1242_ = l_Lean_Parser_ParserState_mkNode(v_s_1229_, v___x_1241_, v_sz_1228_);
lean_dec(v_sz_1228_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1220_;
lean_object* _tmp_6 = v_s_1242_;
v_pOpt_1222_ = _tmp_4;
v_s_1224_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1270_, lean_object* v_sep_1271_, lean_object* v_allowTrailingSep_1272_, lean_object* v_iniSz_1273_, lean_object* v_pOpt_1274_, lean_object* v_c_1275_, lean_object* v_s_1276_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1277_; uint8_t v_pOpt_boxed_1278_; lean_object* v_res_1279_; 
v_allowTrailingSep_boxed_1277_ = lean_unbox(v_allowTrailingSep_1272_);
v_pOpt_boxed_1278_ = lean_unbox(v_pOpt_1274_);
v_res_1279_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1270_, v_sep_1271_, v_allowTrailingSep_boxed_1277_, v_iniSz_1273_, v_pOpt_boxed_1278_, v_c_1275_, v_s_1276_);
lean_dec(v_iniSz_1273_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1280_, lean_object* v_sep_1281_, uint8_t v_allowTrailingSep_1282_, lean_object* v_iniSz_1283_, uint8_t v_pOpt_1284_, lean_object* v_c_1285_, lean_object* v_s_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1280_, v_sep_1281_, v_allowTrailingSep_1282_, v_iniSz_1283_, v_pOpt_1284_, v_c_1285_, v_s_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1288_, lean_object* v_sep_1289_, lean_object* v_allowTrailingSep_1290_, lean_object* v_iniSz_1291_, lean_object* v_pOpt_1292_, lean_object* v_c_1293_, lean_object* v_s_1294_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1295_; uint8_t v_pOpt_boxed_1296_; lean_object* v_res_1297_; 
v_allowTrailingSep_boxed_1295_ = lean_unbox(v_allowTrailingSep_1290_);
v_pOpt_boxed_1296_ = lean_unbox(v_pOpt_1292_);
v_res_1297_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1288_, v_sep_1289_, v_allowTrailingSep_boxed_1295_, v_iniSz_1291_, v_pOpt_boxed_1296_, v_c_1293_, v_s_1294_);
lean_dec(v_iniSz_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1298_, lean_object* v_p_1299_, lean_object* v_sep_1300_, lean_object* v_c_1301_, lean_object* v_s_1302_){
_start:
{
lean_object* v_iniSz_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; 
v_iniSz_1303_ = l_Lean_Parser_ParserState_stackSize(v_s_1302_);
v___x_1304_ = 1;
v___x_1305_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1299_, v_sep_1300_, v_allowTrailingSep_1298_, v_iniSz_1303_, v___x_1304_, v_c_1301_, v_s_1302_);
lean_dec(v_iniSz_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1306_, lean_object* v_p_1307_, lean_object* v_sep_1308_, lean_object* v_c_1309_, lean_object* v_s_1310_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1311_; lean_object* v_res_1312_; 
v_allowTrailingSep_boxed_1311_ = lean_unbox(v_allowTrailingSep_1306_);
v_res_1312_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1311_, v_p_1307_, v_sep_1308_, v_c_1309_, v_s_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1313_, lean_object* v_p_1314_, lean_object* v_sep_1315_, lean_object* v_c_1316_, lean_object* v_s_1317_){
_start:
{
lean_object* v_iniSz_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v_iniSz_1318_ = l_Lean_Parser_ParserState_stackSize(v_s_1317_);
v___x_1319_ = 0;
v___x_1320_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1314_, v_sep_1315_, v_allowTrailingSep_1313_, v_iniSz_1318_, v___x_1319_, v_c_1316_, v_s_1317_);
lean_dec(v_iniSz_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1321_, lean_object* v_p_1322_, lean_object* v_sep_1323_, lean_object* v_c_1324_, lean_object* v_s_1325_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1326_; lean_object* v_res_1327_; 
v_allowTrailingSep_boxed_1326_ = lean_unbox(v_allowTrailingSep_1321_);
v_res_1327_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1326_, v_p_1322_, v_sep_1323_, v_c_1324_, v_s_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1328_, lean_object* v_sep_1329_){
_start:
{
lean_object* v_collectTokens_1330_; lean_object* v_collectKinds_1331_; lean_object* v_collectTokens_1332_; lean_object* v_collectKinds_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1343_; 
v_collectTokens_1330_ = lean_ctor_get(v_p_1328_, 0);
lean_inc_ref(v_collectTokens_1330_);
v_collectKinds_1331_ = lean_ctor_get(v_p_1328_, 1);
lean_inc_ref(v_collectKinds_1331_);
lean_dec_ref(v_p_1328_);
v_collectTokens_1332_ = lean_ctor_get(v_sep_1329_, 0);
v_collectKinds_1333_ = lean_ctor_get(v_sep_1329_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_sep_1329_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_sep_1329_, 2);
lean_dec(v_unused_1344_);
v___x_1335_ = v_sep_1329_;
v_isShared_1336_ = v_isSharedCheck_1343_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_collectKinds_1333_);
lean_inc(v_collectTokens_1332_);
lean_dec(v_sep_1329_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1343_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___f_1337_; lean_object* v___f_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___f_1337_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1337_, 0, v_collectKinds_1333_);
lean_closure_set(v___f_1337_, 1, v_collectKinds_1331_);
v___f_1338_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1338_, 0, v_collectTokens_1332_);
lean_closure_set(v___f_1338_, 1, v_collectTokens_1330_);
v___x_1339_ = lean_box(1);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 2, v___x_1339_);
lean_ctor_set(v___x_1335_, 1, v___f_1337_);
lean_ctor_set(v___x_1335_, 0, v___f_1338_);
v___x_1341_ = v___x_1335_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___f_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___f_1337_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1345_, lean_object* v_sep_1346_){
_start:
{
lean_object* v_collectTokens_1347_; lean_object* v_collectKinds_1348_; lean_object* v_firstTokens_1349_; lean_object* v_collectTokens_1350_; lean_object* v_collectKinds_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1360_; 
v_collectTokens_1347_ = lean_ctor_get(v_p_1345_, 0);
lean_inc_ref(v_collectTokens_1347_);
v_collectKinds_1348_ = lean_ctor_get(v_p_1345_, 1);
lean_inc_ref(v_collectKinds_1348_);
v_firstTokens_1349_ = lean_ctor_get(v_p_1345_, 2);
lean_inc(v_firstTokens_1349_);
lean_dec_ref(v_p_1345_);
v_collectTokens_1350_ = lean_ctor_get(v_sep_1346_, 0);
v_collectKinds_1351_ = lean_ctor_get(v_sep_1346_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_sep_1346_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v_sep_1346_, 2);
lean_dec(v_unused_1361_);
v___x_1353_ = v_sep_1346_;
v_isShared_1354_ = v_isSharedCheck_1360_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_collectKinds_1351_);
lean_inc(v_collectTokens_1350_);
lean_dec(v_sep_1346_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1360_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1358_; 
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1355_, 0, v_collectKinds_1351_);
lean_closure_set(v___f_1355_, 1, v_collectKinds_1348_);
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1356_, 0, v_collectTokens_1350_);
lean_closure_set(v___f_1356_, 1, v_collectTokens_1347_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 2, v_firstTokens_1349_);
lean_ctor_set(v___x_1353_, 1, v___f_1355_);
lean_ctor_set(v___x_1353_, 0, v___f_1356_);
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___f_1356_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___f_1355_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_firstTokens_1349_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1362_, lean_object* v_sep_1363_, uint8_t v_allowTrailingSep_1364_){
_start:
{
lean_object* v_info_1365_; lean_object* v_fn_1366_; lean_object* v_info_1367_; lean_object* v_fn_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1378_; 
v_info_1365_ = lean_ctor_get(v_p_1362_, 0);
lean_inc_ref(v_info_1365_);
v_fn_1366_ = lean_ctor_get(v_p_1362_, 1);
lean_inc_ref(v_fn_1366_);
lean_dec_ref(v_p_1362_);
v_info_1367_ = lean_ctor_get(v_sep_1363_, 0);
v_fn_1368_ = lean_ctor_get(v_sep_1363_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_sep_1363_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1370_ = v_sep_1363_;
v_isShared_1371_ = v_isSharedCheck_1378_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_fn_1368_);
lean_inc(v_info_1367_);
lean_dec(v_sep_1363_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1378_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1372_ = l_Lean_Parser_sepByInfo(v_info_1365_, v_info_1367_);
v___x_1373_ = lean_box(v_allowTrailingSep_1364_);
v___x_1374_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1374_, 0, v___x_1373_);
lean_closure_set(v___x_1374_, 1, v_fn_1366_);
lean_closure_set(v___x_1374_, 2, v_fn_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1374_);
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1376_ = v___x_1370_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1379_, lean_object* v_sep_1380_, lean_object* v_allowTrailingSep_1381_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1382_; lean_object* v_res_1383_; 
v_allowTrailingSep_boxed_1382_ = lean_unbox(v_allowTrailingSep_1381_);
v_res_1383_ = l_Lean_Parser_sepByNoAntiquot(v_p_1379_, v_sep_1380_, v_allowTrailingSep_boxed_1382_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1384_, lean_object* v_sep_1385_, uint8_t v_allowTrailingSep_1386_){
_start:
{
lean_object* v_info_1387_; lean_object* v_fn_1388_; lean_object* v_info_1389_; lean_object* v_fn_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1400_; 
v_info_1387_ = lean_ctor_get(v_p_1384_, 0);
lean_inc_ref(v_info_1387_);
v_fn_1388_ = lean_ctor_get(v_p_1384_, 1);
lean_inc_ref(v_fn_1388_);
lean_dec_ref(v_p_1384_);
v_info_1389_ = lean_ctor_get(v_sep_1385_, 0);
v_fn_1390_ = lean_ctor_get(v_sep_1385_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_sep_1385_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1392_ = v_sep_1385_;
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_fn_1390_);
lean_inc(v_info_1389_);
lean_dec(v_sep_1385_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1394_ = l_Lean_Parser_sepBy1Info(v_info_1387_, v_info_1389_);
v___x_1395_ = lean_box(v_allowTrailingSep_1386_);
v___x_1396_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1396_, 0, v___x_1395_);
lean_closure_set(v___x_1396_, 1, v_fn_1388_);
lean_closure_set(v___x_1396_, 2, v_fn_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___x_1396_);
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1401_, lean_object* v_sep_1402_, lean_object* v_allowTrailingSep_1403_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1404_; lean_object* v_res_1405_; 
v_allowTrailingSep_boxed_1404_ = lean_unbox(v_allowTrailingSep_1403_);
v_res_1405_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1401_, v_sep_1402_, v_allowTrailingSep_boxed_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1406_, lean_object* v_f_1407_, lean_object* v_c_1408_, lean_object* v_s_1409_){
_start:
{
lean_object* v_s_1410_; lean_object* v_stxStack_1411_; lean_object* v_errorMsg_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_s_1410_ = lean_apply_2(v_p_1406_, v_c_1408_, v_s_1409_);
v_stxStack_1411_ = lean_ctor_get(v_s_1410_, 0);
lean_inc_ref(v_stxStack_1411_);
v_errorMsg_1412_ = lean_ctor_get(v_s_1410_, 4);
lean_inc(v_errorMsg_1412_);
v___x_1413_ = lean_box(0);
v___x_1414_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1412_, v___x_1413_);
lean_dec(v_errorMsg_1412_);
if (v___x_1414_ == 0)
{
lean_dec_ref(v_stxStack_1411_);
lean_dec_ref(v_f_1407_);
return v_s_1410_;
}
else
{
lean_object* v_stx_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_stx_1415_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1411_);
lean_dec_ref(v_stxStack_1411_);
v___x_1416_ = l_Lean_Parser_ParserState_popSyntax(v_s_1410_);
v___x_1417_ = lean_apply_1(v_f_1407_, v_stx_1415_);
v___x_1418_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1416_, v___x_1417_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1419_){
_start:
{
lean_object* v_collectTokens_1420_; lean_object* v_collectKinds_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_collectTokens_1420_ = lean_ctor_get(v_p_1419_, 0);
v_collectKinds_1421_ = lean_ctor_get(v_p_1419_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_p_1419_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_p_1419_, 2);
lean_dec(v_unused_1430_);
v___x_1423_ = v_p_1419_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_collectKinds_1421_);
lean_inc(v_collectTokens_1420_);
lean_dec(v_p_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(1);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 2, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_collectTokens_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_collectKinds_1421_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1431_, lean_object* v_f_1432_){
_start:
{
lean_object* v_info_1433_; lean_object* v_fn_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1443_; 
v_info_1433_ = lean_ctor_get(v_p_1431_, 0);
v_fn_1434_ = lean_ctor_get(v_p_1431_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_p_1431_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1436_ = v_p_1431_;
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_fn_1434_);
lean_inc(v_info_1433_);
lean_dec(v_p_1431_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1438_ = l_Lean_Parser_withResultOfInfo(v_info_1433_);
v___x_1439_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1439_, 0, v_fn_1434_);
lean_closure_set(v___x_1439_, 1, v_f_1432_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1439_);
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = l_Lean_Syntax_getNumArgs(v_stx_1444_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_dec_eq(v___x_1445_, v___x_1446_);
lean_dec(v___x_1445_);
if (v___x_1447_ == 0)
{
lean_inc(v_stx_1444_);
return v_stx_1444_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = l_Lean_Syntax_getArg(v_stx_1444_, v___x_1448_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1450_);
lean_dec(v_stx_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1453_){
_start:
{
lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___f_1454_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1455_ = l_Lean_Parser_many1NoAntiquot(v_p_1453_);
v___x_1456_ = l_Lean_Parser_withResultOf(v___x_1455_, v___f_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1457_, lean_object* v_errorMsg_1458_, lean_object* v_c_1459_, lean_object* v_s_1460_){
_start:
{
lean_object* v_pos_1461_; lean_object* v_toInputContext_1462_; uint8_t v___x_1463_; 
v_pos_1461_ = lean_ctor_get(v_s_1460_, 2);
v_toInputContext_1462_ = lean_ctor_get(v_c_1459_, 0);
v___x_1463_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1462_, v_pos_1461_);
if (v___x_1463_ == 0)
{
lean_object* v_inputString_1464_; uint32_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_inputString_1464_ = lean_ctor_get(v_toInputContext_1462_, 0);
v___x_1465_ = lean_string_utf8_get_fast(v_inputString_1464_, v_pos_1461_);
v___x_1466_ = lean_box_uint32(v___x_1465_);
v___x_1467_ = lean_apply_1(v_p_1457_, v___x_1466_);
v___x_1468_ = lean_unbox(v___x_1467_);
if (v___x_1468_ == 0)
{
uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = 1;
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1460_, v_errorMsg_1458_, v___x_1470_, v___x_1469_);
return v___x_1471_;
}
else
{
lean_object* v___x_1472_; 
lean_inc(v_pos_1461_);
lean_dec_ref(v_errorMsg_1458_);
v___x_1472_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1460_, v_c_1459_, v_pos_1461_);
lean_dec(v_pos_1461_);
return v___x_1472_;
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_errorMsg_1458_);
lean_dec_ref(v_p_1457_);
v___x_1473_ = lean_box(0);
v___x_1474_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1460_, v___x_1473_);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1475_, lean_object* v_errorMsg_1476_, lean_object* v_c_1477_, lean_object* v_s_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Parser_satisfyFn(v_p_1475_, v_errorMsg_1476_, v_c_1477_, v_s_1478_);
lean_dec_ref(v_c_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1480_, lean_object* v_c_1481_, lean_object* v_s_1482_){
_start:
{
lean_object* v_pos_1483_; lean_object* v_toInputContext_1484_; uint8_t v___x_1485_; 
v_pos_1483_ = lean_ctor_get(v_s_1482_, 2);
v_toInputContext_1484_ = lean_ctor_get(v_c_1481_, 0);
v___x_1485_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1484_, v_pos_1483_);
if (v___x_1485_ == 0)
{
lean_object* v_inputString_1486_; uint32_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_inputString_1486_ = lean_ctor_get(v_toInputContext_1484_, 0);
v___x_1487_ = lean_string_utf8_get_fast(v_inputString_1486_, v_pos_1483_);
v___x_1488_ = lean_box_uint32(v___x_1487_);
lean_inc_ref(v_p_1480_);
v___x_1489_ = lean_apply_1(v_p_1480_, v___x_1488_);
v___x_1490_ = lean_unbox(v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_inc(v_pos_1483_);
v___x_1491_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1482_, v_c_1481_, v_pos_1483_);
lean_dec(v_pos_1483_);
v_s_1482_ = v___x_1491_;
goto _start;
}
else
{
lean_dec_ref(v_p_1480_);
return v_s_1482_;
}
}
else
{
lean_dec_ref(v_p_1480_);
return v_s_1482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1493_, lean_object* v_c_1494_, lean_object* v_s_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Parser_takeUntilFn(v_p_1493_, v_c_1494_, v_s_1495_);
lean_dec_ref(v_c_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1497_, uint32_t v_c_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_box_uint32(v_c_1498_);
v___x_1500_ = lean_apply_1(v_p_1497_, v___x_1499_);
v___x_1501_ = lean_unbox(v___x_1500_);
if (v___x_1501_ == 0)
{
uint8_t v___x_1502_; 
v___x_1502_ = 1;
return v___x_1502_;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = 0;
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1504_, lean_object* v_c_1505_){
_start:
{
uint32_t v_c_boxed_1506_; uint8_t v_res_1507_; lean_object* v_r_1508_; 
v_c_boxed_1506_ = lean_unbox_uint32(v_c_1505_);
lean_dec(v_c_1505_);
v_res_1507_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1504_, v_c_boxed_1506_);
v_r_1508_ = lean_box(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___f_1512_; lean_object* v___x_1513_; 
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1512_, 0, v_p_1509_);
v___x_1513_ = l_Lean_Parser_takeUntilFn(v___f_1512_, v_a_1510_, v_a_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Parser_takeWhileFn(v_p_1514_, v_a_1515_, v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1518_, lean_object* v_errorMsg_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_inc_ref(v_p_1518_);
v___x_1522_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1522_, 0, v_p_1518_);
lean_closure_set(v___x_1522_, 1, v_errorMsg_1519_);
v___x_1523_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1523_, 0, v_p_1518_);
v___x_1524_ = l_Lean_Parser_andthenFn(v___x_1522_, v___x_1523_, v_a_1520_, v_a_1521_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1526_, lean_object* v_s_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1529_ = lean_box(0);
v___x_1530_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1527_, v___x_1528_, v___x_1529_, v_pushMissingOnError_1526_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1531_, lean_object* v_s_1532_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1533_; lean_object* v_res_1534_; 
v_pushMissingOnError_boxed_1533_ = lean_unbox(v_pushMissingOnError_1531_);
v_res_1534_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1533_, v_s_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1535_, lean_object* v_nesting_1536_, lean_object* v_c_1537_, lean_object* v_s_1538_){
_start:
{
lean_object* v_pos_1539_; lean_object* v_toInputContext_1540_; uint8_t v___x_1541_; 
v_pos_1539_ = lean_ctor_get(v_s_1538_, 2);
v_toInputContext_1540_ = lean_ctor_get(v_c_1537_, 0);
v___x_1541_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1540_, v_pos_1539_);
if (v___x_1541_ == 0)
{
lean_object* v_inputString_1542_; uint32_t v_curr_1543_; lean_object* v_i_1544_; uint32_t v___x_1545_; uint8_t v___x_1546_; 
v_inputString_1542_ = lean_ctor_get(v_toInputContext_1540_, 0);
v_curr_1543_ = lean_string_utf8_get_fast(v_inputString_1542_, v_pos_1539_);
v_i_1544_ = lean_string_utf8_next_fast(v_inputString_1542_, v_pos_1539_);
v___x_1545_ = 45;
v___x_1546_ = lean_uint32_dec_eq(v_curr_1543_, v___x_1545_);
if (v___x_1546_ == 0)
{
uint32_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = 47;
v___x_1548_ = lean_uint32_dec_eq(v_curr_1543_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Parser_ParserState_setPos(v_s_1538_, v_i_1544_);
v_s_1538_ = v___x_1549_;
goto _start;
}
else
{
uint8_t v___x_1551_; 
v___x_1551_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1540_, v_i_1544_);
if (v___x_1551_ == 0)
{
uint32_t v_curr_1552_; uint8_t v___x_1553_; 
v_curr_1552_ = lean_string_utf8_get_fast(v_inputString_1542_, v_i_1544_);
v___x_1553_ = lean_uint32_dec_eq(v_curr_1552_, v___x_1545_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Parser_ParserState_setPos(v_s_1538_, v_i_1544_);
v_s_1538_ = v___x_1554_;
goto _start;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_nesting_1536_, v___x_1556_);
lean_dec(v_nesting_1536_);
v___x_1558_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1538_, v_c_1537_, v_i_1544_);
v_nesting_1536_ = v___x_1557_;
v_s_1538_ = v___x_1558_;
goto _start;
}
}
else
{
lean_object* v___x_1560_; 
lean_dec(v_nesting_1536_);
v___x_1560_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1535_, v_s_1538_);
return v___x_1560_;
}
}
}
else
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1540_, v_i_1544_);
if (v___x_1561_ == 0)
{
uint32_t v_curr_1562_; uint32_t v___x_1563_; uint8_t v___x_1564_; 
v_curr_1562_ = lean_string_utf8_get_fast(v_inputString_1542_, v_i_1544_);
v___x_1563_ = 47;
v___x_1564_ = lean_uint32_dec_eq(v_curr_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Parser_ParserState_setPos(v_s_1538_, v_i_1544_);
v_s_1538_ = v___x_1565_;
goto _start;
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_nat_dec_eq(v_nesting_1536_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_nat_sub(v_nesting_1536_, v___x_1567_);
lean_dec(v_nesting_1536_);
v___x_1570_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1538_, v_c_1537_, v_i_1544_);
v_nesting_1536_ = v___x_1569_;
v_s_1538_ = v___x_1570_;
goto _start;
}
else
{
lean_object* v___x_1572_; 
lean_dec(v_nesting_1536_);
v___x_1572_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1538_, v_c_1537_, v_i_1544_);
return v___x_1572_;
}
}
}
else
{
lean_object* v___x_1573_; 
lean_dec(v_nesting_1536_);
v___x_1573_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1535_, v_s_1538_);
return v___x_1573_;
}
}
}
else
{
lean_object* v___x_1574_; 
lean_dec(v_nesting_1536_);
v___x_1574_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1535_, v_s_1538_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1575_, lean_object* v_nesting_1576_, lean_object* v_c_1577_, lean_object* v_s_1578_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1579_; lean_object* v_res_1580_; 
v_pushMissingOnError_boxed_1579_ = lean_unbox(v_pushMissingOnError_1575_);
v_res_1580_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1579_, v_nesting_1576_, v_c_1577_, v_s_1578_);
lean_dec_ref(v_c_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1581_){
_start:
{
uint32_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = 10;
v___x_1583_ = lean_uint32_dec_eq(v_c_1581_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1584_){
_start:
{
uint32_t v_c_boxed_1585_; uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_c_boxed_1585_ = lean_unbox_uint32(v_c_1584_);
lean_dec(v_c_1584_);
v_res_1586_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1585_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1593_, lean_object* v_s_1594_){
_start:
{
lean_object* v_pos_1595_; lean_object* v_toInputContext_1599_; uint8_t v___x_1600_; 
v_pos_1595_ = lean_ctor_get(v_s_1594_, 2);
v_toInputContext_1599_ = lean_ctor_get(v_c_1593_, 0);
v___x_1600_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1599_, v_pos_1595_);
if (v___x_1600_ == 0)
{
lean_object* v_inputString_1601_; uint32_t v_curr_1602_; uint32_t v___x_1603_; uint8_t v___x_1604_; 
v_inputString_1601_ = lean_ctor_get(v_toInputContext_1599_, 0);
v_curr_1602_ = lean_string_utf8_get_fast(v_inputString_1601_, v_pos_1595_);
v___x_1603_ = 9;
v___x_1604_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
uint32_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = 13;
v___x_1606_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1605_);
if (v___x_1606_ == 0)
{
uint32_t v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = 32;
v___x_1608_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1607_);
if (v___x_1608_ == 0)
{
if (v___x_1604_ == 0)
{
if (v___x_1606_ == 0)
{
uint32_t v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = 10;
v___x_1610_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1609_);
if (v___x_1610_ == 0)
{
uint32_t v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = 45;
v___x_1612_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1611_);
if (v___x_1612_ == 0)
{
uint32_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = 47;
v___x_1614_ = lean_uint32_dec_eq(v_curr_1602_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_dec_ref(v_c_1593_);
return v_s_1594_;
}
else
{
lean_object* v_i_1615_; uint32_t v_curr_1616_; uint8_t v___x_1617_; 
v_i_1615_ = lean_string_utf8_next_fast(v_inputString_1601_, v_pos_1595_);
v_curr_1616_ = lean_string_utf8_get(v_inputString_1601_, v_i_1615_);
v___x_1617_ = lean_uint32_dec_eq(v_curr_1616_, v___x_1611_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v_c_1593_);
return v_s_1594_;
}
else
{
lean_object* v_i_1618_; uint32_t v_curr_1619_; uint8_t v___x_1620_; 
v_i_1618_ = lean_string_utf8_next(v_inputString_1601_, v_i_1615_);
v_curr_1619_ = lean_string_utf8_get(v_inputString_1601_, v_i_1618_);
v___x_1620_ = lean_uint32_dec_eq(v_curr_1619_, v___x_1611_);
if (v___x_1620_ == 0)
{
uint32_t v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = 33;
v___x_1622_ = lean_uint32_dec_eq(v_curr_1619_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1623_ = lean_unsigned_to_nat(1u);
v___x_1624_ = lean_box(v___x_1622_);
v___x_1625_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1625_, 0, v___x_1624_);
lean_closure_set(v___x_1625_, 1, v___x_1623_);
v___x_1626_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1627_ = l_Lean_Parser_ParserState_next(v_s_1594_, v_c_1593_, v_i_1618_);
lean_dec(v_i_1618_);
v___x_1628_ = l_Lean_Parser_andthenFn(v___x_1625_, v___x_1626_, v_c_1593_, v___x_1627_);
return v___x_1628_;
}
else
{
lean_dec(v_i_1618_);
lean_dec_ref(v_c_1593_);
return v_s_1594_;
}
}
else
{
lean_dec(v_i_1618_);
lean_dec_ref(v_c_1593_);
return v_s_1594_;
}
}
}
}
else
{
lean_object* v_i_1629_; uint32_t v_curr_1630_; uint8_t v___x_1631_; 
v_i_1629_ = lean_string_utf8_next_fast(v_inputString_1601_, v_pos_1595_);
v_curr_1630_ = lean_string_utf8_get(v_inputString_1601_, v_i_1629_);
v___x_1631_ = lean_uint32_dec_eq(v_curr_1630_, v___x_1611_);
if (v___x_1631_ == 0)
{
lean_dec_ref(v_c_1593_);
return v_s_1594_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1632_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1633_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1634_ = l_Lean_Parser_ParserState_next(v_s_1594_, v_c_1593_, v_i_1629_);
v___x_1635_ = l_Lean_Parser_andthenFn(v___x_1632_, v___x_1633_, v_c_1593_, v___x_1634_);
return v___x_1635_;
}
}
}
else
{
lean_inc(v_pos_1595_);
goto v___jp_1596_;
}
}
else
{
lean_inc(v_pos_1595_);
goto v___jp_1596_;
}
}
else
{
lean_inc(v_pos_1595_);
goto v___jp_1596_;
}
}
else
{
lean_inc(v_pos_1595_);
goto v___jp_1596_;
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec_ref(v_c_1593_);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1637_ = lean_box(0);
v___x_1638_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1594_, v___x_1636_, v___x_1637_, v___x_1604_);
return v___x_1638_;
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v_c_1593_);
v___x_1639_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1640_ = lean_box(0);
v___x_1641_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1594_, v___x_1639_, v___x_1640_, v___x_1600_);
return v___x_1641_;
}
}
else
{
lean_dec_ref(v_c_1593_);
return v_s_1594_;
}
v___jp_1596_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1594_, v_c_1593_, v_pos_1595_);
lean_dec(v_pos_1595_);
v_s_1594_ = v___x_1597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1642_, lean_object* v_p_1643_){
_start:
{
lean_object* v_toInputContext_1644_; lean_object* v_inputString_1645_; lean_object* v_endPos_1646_; uint8_t v___x_1647_; 
v_toInputContext_1644_ = lean_ctor_get(v_c_1642_, 0);
v_inputString_1645_ = lean_ctor_get(v_toInputContext_1644_, 0);
v_endPos_1646_ = lean_ctor_get(v_toInputContext_1644_, 3);
v___x_1647_ = lean_nat_dec_le(v_p_1643_, v_endPos_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_inc(v_endPos_1646_);
lean_inc_ref(v_inputString_1645_);
v___x_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1648_, 0, v_inputString_1645_);
lean_ctor_set(v___x_1648_, 1, v_p_1643_);
lean_ctor_set(v___x_1648_, 2, v_endPos_1646_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; 
lean_inc(v_p_1643_);
lean_inc_ref(v_inputString_1645_);
v___x_1649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1649_, 0, v_inputString_1645_);
lean_ctor_set(v___x_1649_, 1, v_p_1643_);
lean_ctor_set(v___x_1649_, 2, v_p_1643_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1650_, lean_object* v_p_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1650_, v_p_1651_);
lean_dec_ref(v_c_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1653_, uint8_t v_trailingWs_1654_, lean_object* v_c_1655_, lean_object* v_s_1656_){
_start:
{
lean_object* v_toInputContext_1657_; lean_object* v_pos_1658_; lean_object* v_inputString_1659_; lean_object* v_endPos_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1688_; 
v_toInputContext_1657_ = lean_ctor_get(v_c_1655_, 0);
lean_inc_ref(v_toInputContext_1657_);
v_pos_1658_ = lean_ctor_get(v_s_1656_, 2);
v_inputString_1659_ = lean_ctor_get(v_toInputContext_1657_, 0);
v_endPos_1660_ = lean_ctor_get(v_toInputContext_1657_, 3);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_toInputContext_1657_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1689_ = lean_ctor_get(v_toInputContext_1657_, 2);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_toInputContext_1657_, 1);
lean_dec(v_unused_1690_);
v___x_1662_ = v_toInputContext_1657_;
v_isShared_1663_ = v_isSharedCheck_1688_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_endPos_1660_);
lean_inc(v_inputString_1659_);
lean_dec(v_toInputContext_1657_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1688_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_leading_1664_; lean_object* v_val_1665_; 
lean_inc(v_startPos_1653_);
v_leading_1664_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1655_, v_startPos_1653_);
v_val_1665_ = lean_string_utf8_extract(v_inputString_1659_, v_startPos_1653_, v_pos_1658_);
if (v_trailingWs_1654_ == 0)
{
lean_object* v_trailing_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_dec(v_endPos_1660_);
lean_dec_ref(v_inputString_1659_);
lean_inc(v_pos_1658_);
v_trailing_1666_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1655_, v_pos_1658_);
lean_dec_ref(v_c_1655_);
v___x_1667_ = lean_string_utf8_byte_size(v_val_1665_);
v___x_1668_ = lean_nat_add(v_startPos_1653_, v___x_1667_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 3, v___x_1668_);
lean_ctor_set(v___x_1662_, 2, v_trailing_1666_);
lean_ctor_set(v___x_1662_, 1, v_startPos_1653_);
lean_ctor_set(v___x_1662_, 0, v_leading_1664_);
v___x_1670_ = v___x_1662_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_leading_1664_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_startPos_1653_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_trailing_1666_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v_atom_1671_; lean_object* v___x_1672_; 
v_atom_1671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1671_, 0, v___x_1670_);
lean_ctor_set(v_atom_1671_, 1, v_val_1665_);
v___x_1672_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1656_, v_atom_1671_);
return v___x_1672_;
}
}
else
{
lean_object* v_s_1674_; lean_object* v___y_1676_; lean_object* v_pos_1684_; uint8_t v___x_1685_; 
lean_inc(v_pos_1658_);
v_s_1674_ = l_Lean_Parser_whitespace(v_c_1655_, v_s_1656_);
v_pos_1684_ = lean_ctor_get(v_s_1674_, 2);
v___x_1685_ = lean_nat_dec_le(v_pos_1684_, v_endPos_1660_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1686_, 0, v_inputString_1659_);
lean_ctor_set(v___x_1686_, 1, v_pos_1658_);
lean_ctor_set(v___x_1686_, 2, v_endPos_1660_);
v___y_1676_ = v___x_1686_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1687_; 
lean_dec(v_endPos_1660_);
lean_inc(v_pos_1684_);
v___x_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1687_, 0, v_inputString_1659_);
lean_ctor_set(v___x_1687_, 1, v_pos_1658_);
lean_ctor_set(v___x_1687_, 2, v_pos_1684_);
v___y_1676_ = v___x_1687_;
goto v___jp_1675_;
}
v___jp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1677_ = lean_string_utf8_byte_size(v_val_1665_);
v___x_1678_ = lean_nat_add(v_startPos_1653_, v___x_1677_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 3, v___x_1678_);
lean_ctor_set(v___x_1662_, 2, v___y_1676_);
lean_ctor_set(v___x_1662_, 1, v_startPos_1653_);
lean_ctor_set(v___x_1662_, 0, v_leading_1664_);
v___x_1680_ = v___x_1662_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_leading_1664_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_startPos_1653_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v___y_1676_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v_atom_1681_; lean_object* v___x_1682_; 
v_atom_1681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1681_, 0, v___x_1680_);
lean_ctor_set(v_atom_1681_, 1, v_val_1665_);
v___x_1682_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1674_, v_atom_1681_);
return v___x_1682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1691_, lean_object* v_trailingWs_1692_, lean_object* v_c_1693_, lean_object* v_s_1694_){
_start:
{
uint8_t v_trailingWs_boxed_1695_; lean_object* v_res_1696_; 
v_trailingWs_boxed_1695_ = lean_unbox(v_trailingWs_1692_);
v_res_1696_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1691_, v_trailingWs_boxed_1695_, v_c_1693_, v_s_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1697_, uint8_t v_trailingWs_1698_, lean_object* v_c_1699_, lean_object* v_s_1700_){
_start:
{
lean_object* v_pos_1701_; lean_object* v_s_1702_; lean_object* v_errorMsg_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_pos_1701_ = lean_ctor_get(v_s_1700_, 2);
lean_inc(v_pos_1701_);
lean_inc_ref(v_c_1699_);
v_s_1702_ = lean_apply_2(v_p_1697_, v_c_1699_, v_s_1700_);
v_errorMsg_1703_ = lean_ctor_get(v_s_1702_, 4);
lean_inc(v_errorMsg_1703_);
v___x_1704_ = lean_box(0);
v___x_1705_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1703_, v___x_1704_);
lean_dec(v_errorMsg_1703_);
if (v___x_1705_ == 0)
{
lean_dec(v_pos_1701_);
lean_dec_ref(v_c_1699_);
return v_s_1702_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1701_, v_trailingWs_1698_, v_c_1699_, v_s_1702_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1707_, lean_object* v_trailingWs_1708_, lean_object* v_c_1709_, lean_object* v_s_1710_){
_start:
{
uint8_t v_trailingWs_boxed_1711_; lean_object* v_res_1712_; 
v_trailingWs_boxed_1711_ = lean_unbox(v_trailingWs_1708_);
v_res_1712_ = l_Lean_Parser_rawFn(v_p_1707_, v_trailingWs_boxed_1711_, v_c_1709_, v_s_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1713_, uint32_t v_d_1714_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_uint32_dec_eq(v_c_1713_, v_d_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1716_, lean_object* v_d_1717_){
_start:
{
uint32_t v_c_boxed_1718_; uint32_t v_d_boxed_1719_; uint8_t v_res_1720_; lean_object* v_r_1721_; 
v_c_boxed_1718_ = lean_unbox_uint32(v_c_1716_);
lean_dec(v_c_1716_);
v_d_boxed_1719_ = lean_unbox_uint32(v_d_1717_);
lean_dec(v_d_1717_);
v_res_1720_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1718_, v_d_boxed_1719_);
v_r_1721_ = lean_box(v_res_1720_);
return v_r_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1724_, uint8_t v_trailingWs_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___f_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1728_ = lean_box_uint32(v_c_1724_);
v___f_1729_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1729_, 0, v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1731_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1732_ = lean_string_push(v___x_1731_, v_c_1724_);
v___x_1733_ = lean_string_append(v___x_1730_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_string_append(v___x_1733_, v___x_1730_);
v___x_1735_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1735_, 0, v___f_1729_);
lean_closure_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = l_Lean_Parser_rawFn(v___x_1735_, v_trailingWs_1725_, v_a_1726_, v_a_1727_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1737_, lean_object* v_trailingWs_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
uint32_t v_c_boxed_1741_; uint8_t v_trailingWs_boxed_1742_; lean_object* v_res_1743_; 
v_c_boxed_1741_ = lean_unbox_uint32(v_c_1737_);
lean_dec(v_c_1737_);
v_trailingWs_boxed_1742_ = lean_unbox(v_trailingWs_1738_);
v_res_1743_ = l_Lean_Parser_chFn(v_c_boxed_1741_, v_trailingWs_boxed_1742_, v_a_1739_, v_a_1740_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1744_, uint8_t v_trailingWs_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1746_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1747_ = lean_box_uint32(v_c_1744_);
v___x_1748_ = lean_box(v_trailingWs_1745_);
v___x_1749_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1749_, 0, v___x_1747_);
lean_closure_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1746_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1751_, lean_object* v_trailingWs_1752_){
_start:
{
uint32_t v_c_boxed_1753_; uint8_t v_trailingWs_boxed_1754_; lean_object* v_res_1755_; 
v_c_boxed_1753_ = lean_unbox_uint32(v_c_1751_);
lean_dec(v_c_1751_);
v_trailingWs_boxed_1754_ = lean_unbox(v_trailingWs_1752_);
v_res_1755_ = l_Lean_Parser_rawCh(v_c_boxed_1753_, v_trailingWs_boxed_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1757_, lean_object* v_s_1758_){
_start:
{
lean_object* v_pos_1759_; lean_object* v_toInputContext_1760_; uint8_t v___x_1761_; 
v_pos_1759_ = lean_ctor_get(v_s_1758_, 2);
v_toInputContext_1760_ = lean_ctor_get(v_c_1757_, 0);
v___x_1761_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1760_, v_pos_1759_);
if (v___x_1761_ == 0)
{
lean_object* v_inputString_1762_; uint8_t v___x_1763_; uint32_t v_curr_1764_; lean_object* v_i_1765_; uint8_t v___y_1767_; uint8_t v___y_1773_; uint32_t v___x_1784_; uint8_t v___x_1785_; 
v_inputString_1762_ = lean_ctor_get(v_toInputContext_1760_, 0);
v___x_1763_ = 1;
v_curr_1764_ = lean_string_utf8_get_fast(v_inputString_1762_, v_pos_1759_);
v_i_1765_ = lean_string_utf8_next_fast(v_inputString_1762_, v_pos_1759_);
v___x_1784_ = 48;
v___x_1785_ = lean_uint32_dec_le(v___x_1784_, v_curr_1764_);
if (v___x_1785_ == 0)
{
goto v___jp_1779_;
}
else
{
uint32_t v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = 57;
v___x_1787_ = lean_uint32_dec_le(v_curr_1764_, v___x_1786_);
if (v___x_1787_ == 0)
{
goto v___jp_1779_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Parser_ParserState_setPos(v_s_1758_, v_i_1765_);
return v___x_1788_;
}
}
v___jp_1766_:
{
if (v___y_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1758_, v___x_1768_, v___x_1769_, v___x_1763_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Parser_ParserState_setPos(v_s_1758_, v_i_1765_);
return v___x_1771_;
}
}
v___jp_1772_:
{
if (v___y_1773_ == 0)
{
uint32_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = 65;
v___x_1775_ = lean_uint32_dec_le(v___x_1774_, v_curr_1764_);
if (v___x_1775_ == 0)
{
v___y_1767_ = v___x_1761_;
goto v___jp_1766_;
}
else
{
uint32_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = 70;
v___x_1777_ = lean_uint32_dec_le(v_curr_1764_, v___x_1776_);
v___y_1767_ = v___x_1777_;
goto v___jp_1766_;
}
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Parser_ParserState_setPos(v_s_1758_, v_i_1765_);
return v___x_1778_;
}
}
v___jp_1779_:
{
uint32_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = 97;
v___x_1781_ = lean_uint32_dec_le(v___x_1780_, v_curr_1764_);
if (v___x_1781_ == 0)
{
v___y_1773_ = v___x_1761_;
goto v___jp_1772_;
}
else
{
uint32_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = 102;
v___x_1783_ = lean_uint32_dec_le(v_curr_1764_, v___x_1782_);
v___y_1773_ = v___x_1783_;
goto v___jp_1772_;
}
}
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_box(0);
v___x_1790_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1758_, v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1791_, lean_object* v_s_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Parser_hexDigitFn(v_c_1791_, v_s_1792_);
lean_dec_ref(v_c_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1796_, lean_object* v_c_1797_, lean_object* v_s_1798_){
_start:
{
lean_object* v_pos_1799_; lean_object* v_toInputContext_1803_; uint8_t v___x_1804_; 
v_pos_1799_ = lean_ctor_get(v_s_1798_, 2);
v_toInputContext_1803_ = lean_ctor_get(v_c_1797_, 0);
v___x_1804_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1803_, v_pos_1799_);
if (v___x_1804_ == 0)
{
lean_object* v_inputString_1805_; uint8_t v___x_1806_; uint32_t v_curr_1807_; uint32_t v___x_1808_; uint8_t v___x_1809_; 
v_inputString_1805_ = lean_ctor_get(v_toInputContext_1803_, 0);
v___x_1806_ = 1;
v_curr_1807_ = lean_string_utf8_get_fast(v_inputString_1805_, v_pos_1799_);
v___x_1808_ = 10;
v___x_1809_ = lean_uint32_dec_eq(v_curr_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint32_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = 32;
v___x_1811_ = lean_uint32_dec_eq(v_curr_1807_, v___x_1810_);
if (v___x_1811_ == 0)
{
uint32_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = 9;
v___x_1813_ = lean_uint32_dec_eq(v_curr_1807_, v___x_1812_);
if (v___x_1813_ == 0)
{
uint32_t v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = 13;
v___x_1815_ = lean_uint32_dec_eq(v_curr_1807_, v___x_1814_);
if (v___x_1815_ == 0)
{
if (v___x_1809_ == 0)
{
if (v_seenNewline_1796_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1817_ = lean_box(0);
v___x_1818_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1798_, v___x_1816_, v___x_1817_, v___x_1806_);
return v___x_1818_;
}
else
{
return v_s_1798_;
}
}
else
{
lean_inc(v_pos_1799_);
goto v___jp_1800_;
}
}
else
{
lean_inc(v_pos_1799_);
goto v___jp_1800_;
}
}
else
{
lean_inc(v_pos_1799_);
goto v___jp_1800_;
}
}
else
{
lean_inc(v_pos_1799_);
goto v___jp_1800_;
}
}
else
{
if (v_seenNewline_1796_ == 0)
{
lean_object* v___x_1819_; 
lean_inc(v_pos_1799_);
v___x_1819_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1798_, v_c_1797_, v_pos_1799_);
lean_dec(v_pos_1799_);
v_seenNewline_1796_ = v___x_1806_;
v_s_1798_ = v___x_1819_;
goto _start;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1822_ = lean_box(0);
v___x_1823_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1798_, v___x_1821_, v___x_1822_, v___x_1806_);
return v___x_1823_;
}
}
}
else
{
return v_s_1798_;
}
v___jp_1800_:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1798_, v_c_1797_, v_pos_1799_);
lean_dec(v_pos_1799_);
v_s_1798_ = v___x_1801_;
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
uint32_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = 92;
v___x_1877_ = lean_uint32_dec_eq(v_c_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
uint32_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = 34;
v___x_1879_ = lean_uint32_dec_eq(v_c_1875_, v___x_1878_);
if (v___x_1879_ == 0)
{
uint32_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = 39;
v___x_1881_ = lean_uint32_dec_eq(v_c_1875_, v___x_1880_);
if (v___x_1881_ == 0)
{
uint32_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = 114;
v___x_1883_ = lean_uint32_dec_eq(v_c_1875_, v___x_1882_);
if (v___x_1883_ == 0)
{
uint32_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = 110;
v___x_1885_ = lean_uint32_dec_eq(v_c_1875_, v___x_1884_);
if (v___x_1885_ == 0)
{
uint32_t v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = 116;
v___x_1887_ = lean_uint32_dec_eq(v_c_1875_, v___x_1886_);
return v___x_1887_;
}
else
{
return v___x_1885_;
}
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
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1888_){
_start:
{
uint32_t v_c_boxed_1889_; uint8_t v_res_1890_; lean_object* v_r_1891_; 
v_c_boxed_1889_ = lean_unbox_uint32(v_c_1888_);
lean_dec(v_c_1888_);
v_res_1890_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1889_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1896_ = 0;
v___x_1897_ = l_Lean_Parser_quotedCharCoreFn(v___x_1895_, v___x_1896_, v_a_1893_, v_a_1894_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1901_ = 1;
v___x_1902_ = l_Lean_Parser_quotedCharCoreFn(v___x_1900_, v___x_1901_, v_a_1898_, v_a_1899_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1903_, lean_object* v_startPos_1904_, uint8_t v_includeWhitespace_1905_, lean_object* v_c_1906_, lean_object* v_s_1907_){
_start:
{
lean_object* v_pos_1908_; lean_object* v_errorMsg_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_pos_1908_ = lean_ctor_get(v_s_1907_, 2);
v_errorMsg_1909_ = lean_ctor_get(v_s_1907_, 4);
v___x_1910_ = lean_box(0);
v___x_1911_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_c_1906_);
lean_dec(v_startPos_1904_);
lean_dec(v_n_1903_);
return v_s_1907_;
}
else
{
lean_object* v_toInputContext_1912_; lean_object* v_inputString_1913_; lean_object* v_endPos_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1936_; 
lean_inc(v_pos_1908_);
v_toInputContext_1912_ = lean_ctor_get(v_c_1906_, 0);
lean_inc_ref(v_toInputContext_1912_);
v_inputString_1913_ = lean_ctor_get(v_toInputContext_1912_, 0);
v_endPos_1914_ = lean_ctor_get(v_toInputContext_1912_, 3);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_toInputContext_1912_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; lean_object* v_unused_1938_; 
v_unused_1937_ = lean_ctor_get(v_toInputContext_1912_, 2);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_toInputContext_1912_, 1);
lean_dec(v_unused_1938_);
v___x_1916_ = v_toInputContext_1912_;
v_isShared_1917_ = v_isSharedCheck_1936_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_endPos_1914_);
lean_inc(v_inputString_1913_);
lean_dec(v_toInputContext_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1936_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_leading_1918_; lean_object* v_val_1919_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1929_; lean_object* v_pos_1930_; 
lean_inc(v_startPos_1904_);
v_leading_1918_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1906_, v_startPos_1904_);
v_val_1919_ = lean_string_utf8_extract(v_inputString_1913_, v_startPos_1904_, v_pos_1908_);
if (v_includeWhitespace_1905_ == 0)
{
lean_dec_ref(v_c_1906_);
lean_inc(v_pos_1908_);
v___y_1929_ = v_s_1907_;
v_pos_1930_ = v_pos_1908_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1934_; lean_object* v_pos_1935_; 
v___x_1934_ = l_Lean_Parser_whitespace(v_c_1906_, v_s_1907_);
v_pos_1935_ = lean_ctor_get(v___x_1934_, 2);
lean_inc(v_pos_1935_);
v___y_1929_ = v___x_1934_;
v_pos_1930_ = v_pos_1935_;
goto v___jp_1928_;
}
v___jp_1920_:
{
lean_object* v_info_1924_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 3, v_pos_1908_);
lean_ctor_set(v___x_1916_, 2, v___y_1922_);
lean_ctor_set(v___x_1916_, 1, v_startPos_1904_);
lean_ctor_set(v___x_1916_, 0, v_leading_1918_);
v_info_1924_ = v___x_1916_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_leading_1918_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_startPos_1904_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v___y_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_pos_1908_);
v_info_1924_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = l_Lean_Syntax_mkLit(v_n_1903_, v_val_1919_, v_info_1924_);
v___x_1926_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1921_, v___x_1925_);
return v___x_1926_;
}
}
v___jp_1928_:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_nat_dec_le(v_pos_1930_, v_endPos_1914_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec(v_pos_1930_);
lean_inc(v_pos_1908_);
v___x_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1932_, 0, v_inputString_1913_);
lean_ctor_set(v___x_1932_, 1, v_pos_1908_);
lean_ctor_set(v___x_1932_, 2, v_endPos_1914_);
v___y_1921_ = v___y_1929_;
v___y_1922_ = v___x_1932_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1933_; 
lean_dec(v_endPos_1914_);
lean_inc(v_pos_1908_);
v___x_1933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1933_, 0, v_inputString_1913_);
lean_ctor_set(v___x_1933_, 1, v_pos_1908_);
lean_ctor_set(v___x_1933_, 2, v_pos_1930_);
v___y_1921_ = v___y_1929_;
v___y_1922_ = v___x_1933_;
goto v___jp_1920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1939_, lean_object* v_startPos_1940_, lean_object* v_includeWhitespace_1941_, lean_object* v_c_1942_, lean_object* v_s_1943_){
_start:
{
uint8_t v_includeWhitespace_boxed_1944_; lean_object* v_res_1945_; 
v_includeWhitespace_boxed_1944_ = lean_unbox(v_includeWhitespace_1941_);
v_res_1945_ = l_Lean_Parser_mkNodeToken(v_n_1939_, v_startPos_1940_, v_includeWhitespace_boxed_1944_, v_c_1942_, v_s_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1950_, lean_object* v_c_1951_, lean_object* v_s_1952_){
_start:
{
lean_object* v_pos_1953_; lean_object* v_toInputContext_1954_; uint8_t v___x_1955_; 
v_pos_1953_ = lean_ctor_get(v_s_1952_, 2);
v_toInputContext_1954_ = lean_ctor_get(v_c_1951_, 0);
v___x_1955_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1954_, v_pos_1953_);
if (v___x_1955_ == 0)
{
lean_object* v_inputString_1956_; uint8_t v___x_1957_; lean_object* v___y_1959_; uint32_t v_curr_1974_; lean_object* v___x_1975_; lean_object* v_s_1976_; uint32_t v___x_1977_; uint8_t v___x_1978_; 
v_inputString_1956_ = lean_ctor_get(v_toInputContext_1954_, 0);
v___x_1957_ = 1;
v_curr_1974_ = lean_string_utf8_get_fast(v_inputString_1956_, v_pos_1953_);
v___x_1975_ = lean_string_utf8_next_fast(v_inputString_1956_, v_pos_1953_);
v_s_1976_ = l_Lean_Parser_ParserState_setPos(v_s_1952_, v___x_1975_);
v___x_1977_ = 92;
v___x_1978_ = lean_uint32_dec_eq(v_curr_1974_, v___x_1977_);
if (v___x_1978_ == 0)
{
v___y_1959_ = v_s_1976_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1979_; 
lean_inc_ref(v_c_1951_);
v___x_1979_ = l_Lean_Parser_quotedCharFn(v_c_1951_, v_s_1976_);
v___y_1959_ = v___x_1979_;
goto v___jp_1958_;
}
v___jp_1958_:
{
lean_object* v_pos_1960_; lean_object* v_errorMsg_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_pos_1960_ = lean_ctor_get(v___y_1959_, 2);
v_errorMsg_1961_ = lean_ctor_get(v___y_1959_, 4);
v___x_1962_ = lean_box(0);
v___x_1963_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_dec_ref(v_c_1951_);
lean_dec(v_startPos_1950_);
return v___y_1959_;
}
else
{
if (v___x_1955_ == 0)
{
uint32_t v_curr_1964_; lean_object* v___x_1965_; lean_object* v_s_1966_; uint32_t v___x_1967_; uint8_t v___x_1968_; 
v_curr_1964_ = lean_string_utf8_get(v_inputString_1956_, v_pos_1960_);
v___x_1965_ = lean_string_utf8_next(v_inputString_1956_, v_pos_1960_);
v_s_1966_ = l_Lean_Parser_ParserState_setPos(v___y_1959_, v___x_1965_);
v___x_1967_ = 39;
v___x_1968_ = lean_uint32_dec_eq(v_curr_1964_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_c_1951_);
lean_dec(v_startPos_1950_);
v___x_1969_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1970_ = lean_box(0);
v___x_1971_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1966_, v___x_1969_, v___x_1970_, v___x_1957_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1973_ = l_Lean_Parser_mkNodeToken(v___x_1972_, v_startPos_1950_, v___x_1957_, v_c_1951_, v_s_1966_);
return v___x_1973_;
}
}
else
{
lean_dec_ref(v_c_1951_);
lean_dec(v_startPos_1950_);
return v___y_1959_;
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec_ref(v_c_1951_);
lean_dec(v_startPos_1950_);
v___x_1980_ = lean_box(0);
v___x_1981_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1952_, v___x_1980_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_1986_, lean_object* v_includeWhitespace_1987_, lean_object* v_c_1988_, lean_object* v_s_1989_){
_start:
{
uint8_t v_includeWhitespace_boxed_1990_; lean_object* v_res_1991_; 
v_includeWhitespace_boxed_1990_ = lean_unbox(v_includeWhitespace_1987_);
v_res_1991_ = l_Lean_Parser_strLitFnAux(v_startPos_1986_, v_includeWhitespace_boxed_1990_, v_c_1988_, v_s_1989_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_1992_, uint8_t v_includeWhitespace_1993_, lean_object* v_c_1994_, lean_object* v_s_1995_){
_start:
{
lean_object* v_pos_1996_; lean_object* v_toInputContext_1997_; uint8_t v___x_1998_; 
v_pos_1996_ = lean_ctor_get(v_s_1995_, 2);
v_toInputContext_1997_ = lean_ctor_get(v_c_1994_, 0);
v___x_1998_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1997_, v_pos_1996_);
if (v___x_1998_ == 0)
{
lean_object* v_inputString_1999_; uint32_t v_curr_2000_; lean_object* v___x_2001_; lean_object* v_s_2002_; uint32_t v___x_2003_; uint8_t v___x_2004_; 
v_inputString_1999_ = lean_ctor_get(v_toInputContext_1997_, 0);
v_curr_2000_ = lean_string_utf8_get_fast(v_inputString_1999_, v_pos_1996_);
v___x_2001_ = lean_string_utf8_next_fast(v_inputString_1999_, v_pos_1996_);
v_s_2002_ = l_Lean_Parser_ParserState_setPos(v_s_1995_, v___x_2001_);
v___x_2003_ = 34;
v___x_2004_ = lean_uint32_dec_eq(v_curr_2000_, v___x_2003_);
if (v___x_2004_ == 0)
{
uint32_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = 92;
v___x_2006_ = lean_uint32_dec_eq(v_curr_2000_, v___x_2005_);
if (v___x_2006_ == 0)
{
v_s_1995_ = v_s_2002_;
goto _start;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2009_ = lean_box(v_includeWhitespace_1993_);
v___x_2010_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2010_, 0, v_startPos_1992_);
lean_closure_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Lean_Parser_andthenFn(v___x_2008_, v___x_2010_, v_c_1994_, v_s_2002_);
return v___x_2011_;
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2013_ = l_Lean_Parser_mkNodeToken(v___x_2012_, v_startPos_1992_, v_includeWhitespace_1993_, v_c_1994_, v_s_2002_);
return v___x_2013_;
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec_ref(v_c_1994_);
v___x_2014_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2015_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_1995_, v___x_2014_, v_startPos_1992_);
return v___x_2015_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2016_, lean_object* v_i_2017_){
_start:
{
lean_object* v_toInputContext_2018_; uint8_t v___x_2019_; 
v_toInputContext_2018_ = lean_ctor_get(v_c_2016_, 0);
v___x_2019_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2018_, v_i_2017_);
if (v___x_2019_ == 0)
{
lean_object* v_inputString_2020_; uint32_t v_curr_2021_; uint32_t v___x_2022_; uint8_t v___x_2023_; 
v_inputString_2020_ = lean_ctor_get(v_toInputContext_2018_, 0);
v_curr_2021_ = lean_string_utf8_get_fast(v_inputString_2020_, v_i_2017_);
v___x_2022_ = 35;
v___x_2023_ = lean_uint32_dec_eq(v_curr_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
uint32_t v___x_2024_; uint8_t v___x_2025_; 
lean_dec(v_i_2017_);
v___x_2024_ = 34;
v___x_2025_ = lean_uint32_dec_eq(v_curr_2021_, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_string_utf8_next_fast(v_inputString_2020_, v_i_2017_);
lean_dec(v_i_2017_);
v_i_2017_ = v___x_2026_;
goto _start;
}
}
else
{
uint8_t v___x_2028_; 
lean_dec(v_i_2017_);
v___x_2028_ = 0;
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2029_, lean_object* v_i_2030_){
_start:
{
uint8_t v_res_2031_; lean_object* v_r_2032_; 
v_res_2031_ = l_Lean_Parser_isRawStrLitStart(v_c_2029_, v_i_2030_);
lean_dec_ref(v_c_2029_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2034_, lean_object* v_s_2035_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2037_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2035_, v___x_2036_, v_startPos_2034_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2038_, lean_object* v_num_2039_, lean_object* v_closingNum_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_pos_2043_; lean_object* v_toInputContext_2044_; uint8_t v___x_2045_; 
v_pos_2043_ = lean_ctor_get(v_a_2042_, 2);
v_toInputContext_2044_ = lean_ctor_get(v_a_2041_, 0);
v___x_2045_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2044_, v_pos_2043_);
if (v___x_2045_ == 0)
{
lean_object* v_inputString_2046_; uint32_t v_curr_2047_; lean_object* v___x_2048_; lean_object* v_s_2049_; uint32_t v___x_2050_; uint8_t v___x_2051_; 
v_inputString_2046_ = lean_ctor_get(v_toInputContext_2044_, 0);
v_curr_2047_ = lean_string_utf8_get_fast(v_inputString_2046_, v_pos_2043_);
v___x_2048_ = lean_string_utf8_next_fast(v_inputString_2046_, v_pos_2043_);
v_s_2049_ = l_Lean_Parser_ParserState_setPos(v_a_2042_, v___x_2048_);
v___x_2050_ = 35;
v___x_2051_ = lean_uint32_dec_eq(v_curr_2047_, v___x_2050_);
if (v___x_2051_ == 0)
{
uint32_t v___x_2052_; uint8_t v___x_2053_; 
lean_dec(v_closingNum_2040_);
v___x_2052_ = 34;
v___x_2053_ = lean_uint32_dec_eq(v_curr_2047_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2038_, v_num_2039_, v_a_2041_, v_s_2049_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v_closingNum_2040_ = v___x_2055_;
v_a_2042_ = v_s_2049_;
goto _start;
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_nat_add(v_closingNum_2040_, v___x_2057_);
lean_dec(v_closingNum_2040_);
v___x_2059_ = lean_nat_dec_eq(v___x_2058_, v_num_2039_);
if (v___x_2059_ == 0)
{
v_closingNum_2040_ = v___x_2058_;
v_a_2042_ = v_s_2049_;
goto _start;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v___x_2058_);
v___x_2061_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2062_ = l_Lean_Parser_mkNodeToken(v___x_2061_, v_startPos_2038_, v___x_2059_, v_a_2041_, v_s_2049_);
return v___x_2062_;
}
}
}
else
{
lean_object* v___x_2063_; 
lean_dec_ref(v_a_2041_);
lean_dec(v_closingNum_2040_);
v___x_2063_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2038_, v_a_2042_);
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2064_, lean_object* v_num_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
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
v___x_2075_ = 34;
v___x_2076_ = lean_uint32_dec_eq(v_curr_2072_, v___x_2075_);
if (v___x_2076_ == 0)
{
v_a_2067_ = v_s_2074_;
goto _start;
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_nat_dec_eq(v_num_2065_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2064_, v_num_2065_, v___x_2078_, v_a_2066_, v_s_2074_);
return v___x_2080_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2082_ = l_Lean_Parser_mkNodeToken(v___x_2081_, v_startPos_2064_, v___x_2079_, v_a_2066_, v_s_2074_);
return v___x_2082_;
}
}
}
else
{
lean_object* v___x_2083_; 
lean_dec_ref(v_a_2066_);
v___x_2083_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2064_, v_a_2067_);
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2084_, lean_object* v_num_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2084_, v_num_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_num_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2089_, lean_object* v_num_2090_, lean_object* v_closingNum_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2089_, v_num_2090_, v_closingNum_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_num_2090_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2095_, lean_object* v_num_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_pos_2099_; lean_object* v_toInputContext_2100_; uint8_t v___x_2101_; 
v_pos_2099_ = lean_ctor_get(v_a_2098_, 2);
v_toInputContext_2100_ = lean_ctor_get(v_a_2097_, 0);
v___x_2101_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2100_, v_pos_2099_);
if (v___x_2101_ == 0)
{
lean_object* v_inputString_2102_; uint32_t v_curr_2103_; lean_object* v___x_2104_; lean_object* v_s_2105_; uint32_t v___x_2106_; uint8_t v___x_2107_; 
v_inputString_2102_ = lean_ctor_get(v_toInputContext_2100_, 0);
v_curr_2103_ = lean_string_utf8_get_fast(v_inputString_2102_, v_pos_2099_);
v___x_2104_ = lean_string_utf8_next_fast(v_inputString_2102_, v_pos_2099_);
v_s_2105_ = l_Lean_Parser_ParserState_setPos(v_a_2098_, v___x_2104_);
v___x_2106_ = 35;
v___x_2107_ = lean_uint32_dec_eq(v_curr_2103_, v___x_2106_);
if (v___x_2107_ == 0)
{
uint32_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = 34;
v___x_2109_ = lean_uint32_dec_eq(v_curr_2103_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v_a_2097_);
lean_dec(v_num_2096_);
v___x_2110_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2095_, v_s_2105_);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2095_, v_num_2096_, v_a_2097_, v_s_2105_);
lean_dec(v_num_2096_);
return v___x_2111_;
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_nat_add(v_num_2096_, v___x_2112_);
lean_dec(v_num_2096_);
v_num_2096_ = v___x_2113_;
v_a_2098_ = v_s_2105_;
goto _start;
}
}
else
{
lean_object* v___x_2115_; 
lean_dec_ref(v_a_2097_);
lean_dec(v_num_2096_);
v___x_2115_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2095_, v_a_2098_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2116_, v___x_2119_, v_a_2117_, v_a_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2122_, lean_object* v_expecting_2123_, uint8_t v_needDigit_2124_, lean_object* v_c_2125_, lean_object* v_s_2126_){
_start:
{
lean_object* v_pos_2127_; lean_object* v_toInputContext_2128_; uint8_t v___x_2129_; 
v_pos_2127_ = lean_ctor_get(v_s_2126_, 2);
v_toInputContext_2128_ = lean_ctor_get(v_c_2125_, 0);
v___x_2129_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2128_, v_pos_2127_);
if (v___x_2129_ == 0)
{
lean_object* v_inputString_2130_; uint8_t v___x_2131_; uint32_t v_curr_2132_; uint32_t v___x_2133_; uint8_t v___x_2134_; 
v_inputString_2130_ = lean_ctor_get(v_toInputContext_2128_, 0);
v___x_2131_ = 1;
v_curr_2132_ = lean_string_utf8_get_fast(v_inputString_2130_, v_pos_2127_);
v___x_2133_ = 95;
v___x_2134_ = lean_uint32_dec_eq(v_curr_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2135_ = lean_box_uint32(v_curr_2132_);
lean_inc_ref(v_isDigit_2122_);
v___x_2136_ = lean_apply_1(v_isDigit_2122_, v___x_2135_);
v___x_2137_ = lean_unbox(v___x_2136_);
if (v___x_2137_ == 0)
{
lean_dec_ref(v_isDigit_2122_);
if (v_needDigit_2124_ == 0)
{
lean_dec_ref(v_expecting_2123_);
return v_s_2126_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2138_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_expecting_2123_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2126_, v___x_2138_, v___x_2140_, v___x_2131_);
return v___x_2141_;
}
}
else
{
lean_object* v___x_2142_; 
lean_inc(v_pos_2127_);
v___x_2142_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2126_, v_c_2125_, v_pos_2127_);
lean_dec(v_pos_2127_);
v_needDigit_2124_ = v___x_2134_;
v_s_2126_ = v___x_2142_;
goto _start;
}
}
else
{
lean_object* v___x_2144_; 
lean_inc(v_pos_2127_);
v___x_2144_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2126_, v_c_2125_, v_pos_2127_);
lean_dec(v_pos_2127_);
v_needDigit_2124_ = v___x_2131_;
v_s_2126_ = v___x_2144_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2122_);
if (v_needDigit_2124_ == 0)
{
lean_dec_ref(v_expecting_2123_);
return v_s_2126_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_expecting_2123_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2126_, v___x_2147_);
return v___x_2148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2149_, lean_object* v_expecting_2150_, lean_object* v_needDigit_2151_, lean_object* v_c_2152_, lean_object* v_s_2153_){
_start:
{
uint8_t v_needDigit_boxed_2154_; lean_object* v_res_2155_; 
v_needDigit_boxed_2154_ = lean_unbox(v_needDigit_2151_);
v_res_2155_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2149_, v_expecting_2150_, v_needDigit_boxed_2154_, v_c_2152_, v_s_2153_);
lean_dec_ref(v_c_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2156_){
_start:
{
uint32_t v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = 48;
v___x_2158_ = lean_uint32_dec_le(v___x_2157_, v_c_2156_);
if (v___x_2158_ == 0)
{
return v___x_2158_;
}
else
{
uint32_t v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = 57;
v___x_2160_ = lean_uint32_dec_le(v_c_2156_, v___x_2159_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2161_){
_start:
{
uint32_t v_c_boxed_2162_; uint8_t v_res_2163_; lean_object* v_r_2164_; 
v_c_boxed_2162_ = lean_unbox_uint32(v_c_2161_);
lean_dec(v_c_2161_);
v_res_2163_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2162_);
v_r_2164_ = lean_box(v_res_2163_);
return v_r_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2169_, lean_object* v_c_2170_, lean_object* v_s_2171_, uint8_t v_hasBareDot_2172_){
_start:
{
lean_object* v_toInputContext_2173_; lean_object* v_pos_2174_; uint8_t v___x_2175_; 
v_toInputContext_2173_ = lean_ctor_get(v_c_2170_, 0);
v_pos_2174_ = lean_ctor_get(v_s_2171_, 2);
v___x_2175_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2173_, v_pos_2174_);
if (v___x_2175_ == 0)
{
lean_object* v_inputString_2176_; lean_object* v___f_2177_; uint8_t v___x_2178_; lean_object* v___y_2184_; lean_object* v___y_2194_; lean_object* v___y_2195_; uint32_t v_curr_2209_; uint32_t v___x_2221_; uint8_t v___x_2222_; 
v_inputString_2176_ = lean_ctor_get(v_toInputContext_2173_, 0);
v___f_2177_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2178_ = 1;
v_curr_2209_ = lean_string_utf8_get_fast(v_inputString_2176_, v_pos_2174_);
v___x_2221_ = 101;
v___x_2222_ = lean_uint32_dec_eq(v_curr_2209_, v___x_2221_);
if (v___x_2222_ == 0)
{
uint32_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = 69;
v___x_2224_ = lean_uint32_dec_eq(v_curr_2209_, v___x_2223_);
if (v___x_2224_ == 0)
{
if (v_hasBareDot_2172_ == 0)
{
lean_dec(v_startPos_2169_);
return v_s_2171_;
}
else
{
uint32_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = 65;
v___x_2226_ = lean_uint32_dec_le(v___x_2225_, v_curr_2209_);
if (v___x_2226_ == 0)
{
goto v___jp_2216_;
}
else
{
uint32_t v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = 90;
v___x_2228_ = lean_uint32_dec_le(v_curr_2209_, v___x_2227_);
if (v___x_2228_ == 0)
{
goto v___jp_2216_;
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
lean_dec(v_startPos_2169_);
goto v___jp_2197_;
}
}
else
{
lean_dec(v_startPos_2169_);
goto v___jp_2197_;
}
v___jp_2179_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2171_, v___x_2180_, v___x_2181_, v___x_2178_);
return v___x_2182_;
}
v___jp_2183_:
{
uint32_t v_curr_2185_; uint32_t v___x_2186_; uint8_t v___x_2187_; 
v_curr_2185_ = lean_string_utf8_get(v_inputString_2176_, v___y_2184_);
v___x_2186_ = 48;
v___x_2187_ = lean_uint32_dec_le(v___x_2186_, v_curr_2185_);
if (v___x_2187_ == 0)
{
lean_dec(v___y_2184_);
goto v___jp_2179_;
}
else
{
uint32_t v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = 57;
v___x_2189_ = lean_uint32_dec_le(v_curr_2185_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_dec(v___y_2184_);
goto v___jp_2179_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2191_ = l_Lean_Parser_ParserState_setPos(v_s_2171_, v___y_2184_);
v___x_2192_ = l_Lean_Parser_takeDigitsFn(v___f_2177_, v___x_2190_, v___x_2175_, v_c_2170_, v___x_2191_);
return v___x_2192_;
}
}
}
v___jp_2193_:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_string_utf8_next(v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
v___y_2184_ = v___x_2196_;
goto v___jp_2183_;
}
v___jp_2197_:
{
lean_object* v_i_2198_; uint32_t v___x_2199_; uint32_t v___x_2200_; uint8_t v___x_2201_; 
v_i_2198_ = lean_string_utf8_next(v_inputString_2176_, v_pos_2174_);
v___x_2199_ = lean_string_utf8_get(v_inputString_2176_, v_i_2198_);
v___x_2200_ = 45;
v___x_2201_ = lean_uint32_dec_eq(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
uint32_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = 43;
v___x_2203_ = lean_uint32_dec_eq(v___x_2199_, v___x_2202_);
if (v___x_2203_ == 0)
{
v___y_2184_ = v_i_2198_;
goto v___jp_2183_;
}
else
{
v___y_2194_ = v_inputString_2176_;
v___y_2195_ = v_i_2198_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v_inputString_2176_;
v___y_2195_ = v_i_2198_;
goto v___jp_2193_;
}
}
v___jp_2204_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lean_Parser_ParserState_setPos(v_s_2171_, v_startPos_2169_);
v___x_2206_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2207_ = lean_box(0);
v___x_2208_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2205_, v___x_2206_, v___x_2207_, v___x_2178_);
return v___x_2208_;
}
v___jp_2210_:
{
uint32_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = 95;
v___x_2212_ = lean_uint32_dec_eq(v_curr_2209_, v___x_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; 
v___x_2213_ = l_Lean_isLetterLike(v_curr_2209_);
if (v___x_2213_ == 0)
{
uint32_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = l_Lean_idBeginEscape;
v___x_2215_ = lean_uint32_dec_eq(v_curr_2209_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_dec(v_startPos_2169_);
return v_s_2171_;
}
else
{
goto v___jp_2204_;
}
}
else
{
goto v___jp_2204_;
}
}
else
{
goto v___jp_2204_;
}
}
v___jp_2216_:
{
uint32_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = 97;
v___x_2218_ = lean_uint32_dec_le(v___x_2217_, v_curr_2209_);
if (v___x_2218_ == 0)
{
goto v___jp_2210_;
}
else
{
uint32_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = 122;
v___x_2220_ = lean_uint32_dec_le(v_curr_2209_, v___x_2219_);
if (v___x_2220_ == 0)
{
goto v___jp_2210_;
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
lean_dec(v_startPos_2169_);
return v_s_2171_;
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
v_toInputContext_2297_ = lean_ctor_get(v_c_2290_, 0);
v___x_2298_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2297_, v_pos_2296_);
if (v___x_2298_ == 0)
{
lean_object* v_inputString_2299_; uint32_t v_curr_2300_; lean_object* v_j_2313_; uint8_t v___x_2321_; 
v_inputString_2299_ = lean_ctor_get(v_toInputContext_2297_, 0);
v_curr_2300_ = lean_string_utf8_get_fast(v_inputString_2299_, v_pos_2296_);
v_j_2313_ = lean_string_utf8_next(v_inputString_2299_, v_pos_2296_);
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
uint32_t v___y_110__boxed_2419_; uint8_t v_res_2420_; lean_object* v_r_2421_; 
v___y_110__boxed_2419_ = lean_unbox_uint32(v___y_2418_);
lean_dec(v___y_2418_);
v_res_2420_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_110__boxed_2419_);
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
uint32_t v_curr_2503_; uint32_t v___x_2515_; uint8_t v___x_2516_; 
v_curr_2503_ = lean_string_utf8_get(v_inputString_2497_, v_i_2501_);
lean_dec(v_i_2501_);
v___x_2515_ = 65;
v___x_2516_ = lean_uint32_dec_le(v___x_2515_, v_curr_2503_);
if (v___x_2516_ == 0)
{
goto v___jp_2510_;
}
else
{
uint32_t v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = 90;
v___x_2518_ = lean_uint32_dec_le(v_curr_2503_, v___x_2517_);
if (v___x_2518_ == 0)
{
goto v___jp_2510_;
}
else
{
return v___x_2500_;
}
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
v___x_2508_ = l_Lean_idBeginEscape;
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
uint32_t v___x_2511_; uint8_t v___x_2512_; 
v___x_2511_ = 97;
v___x_2512_ = lean_uint32_dec_le(v___x_2511_, v_curr_2503_);
if (v___x_2512_ == 0)
{
goto v___jp_2504_;
}
else
{
uint32_t v___x_2513_; uint8_t v___x_2514_; 
v___x_2513_ = 122;
v___x_2514_ = lean_uint32_dec_le(v_curr_2503_, v___x_2513_);
if (v___x_2514_ == 0)
{
goto v___jp_2504_;
}
else
{
return v___x_2500_;
}
}
}
}
else
{
uint8_t v___x_2519_; 
lean_dec(v_i_2501_);
v___x_2519_ = 0;
return v___x_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2520_, lean_object* v_s_2521_){
_start:
{
uint8_t v_res_2522_; lean_object* v_r_2523_; 
v_res_2522_ = l_Lean_Parser_isIdCont(v_c_2520_, v_s_2521_);
lean_dec_ref(v_s_2521_);
lean_dec_ref(v_c_2520_);
v_r_2523_ = lean_box(v_res_2522_);
return v_r_2523_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2524_, lean_object* v_idStopPos_2525_, lean_object* v_tk_2526_){
_start:
{
if (lean_obj_tag(v_tk_2526_) == 0)
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
else
{
lean_object* v_val_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_val_2528_ = lean_ctor_get(v_tk_2526_, 0);
v___x_2529_ = lean_nat_sub(v_idStopPos_2525_, v_idStartPos_2524_);
v___x_2530_ = lean_string_utf8_byte_size(v_val_2528_);
v___x_2531_ = lean_nat_dec_le(v___x_2529_, v___x_2530_);
lean_dec(v___x_2529_);
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2532_, lean_object* v_idStopPos_2533_, lean_object* v_tk_2534_){
_start:
{
uint8_t v_res_2535_; lean_object* v_r_2536_; 
v_res_2535_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2532_, v_idStopPos_2533_, v_tk_2534_);
lean_dec(v_tk_2534_);
lean_dec(v_idStopPos_2533_);
lean_dec(v_idStartPos_2532_);
v_r_2536_ = lean_box(v_res_2535_);
return v_r_2536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object* v_a_2537_, lean_object* v_as_2538_, size_t v_i_2539_, size_t v_stop_2540_){
_start:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_usize_dec_eq(v_i_2539_, v_stop_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = lean_array_uget_borrowed(v_as_2538_, v_i_2539_);
v___x_2543_ = lean_string_dec_eq(v_a_2537_, v___x_2542_);
if (v___x_2543_ == 0)
{
size_t v___x_2544_; size_t v___x_2545_; 
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_add(v_i_2539_, v___x_2544_);
v_i_2539_ = v___x_2545_;
goto _start;
}
else
{
return v___x_2543_;
}
}
else
{
uint8_t v___x_2547_; 
v___x_2547_ = 0;
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object* v_a_2548_, lean_object* v_as_2549_, lean_object* v_i_2550_, lean_object* v_stop_2551_){
_start:
{
size_t v_i_boxed_2552_; size_t v_stop_boxed_2553_; uint8_t v_res_2554_; lean_object* v_r_2555_; 
v_i_boxed_2552_ = lean_unbox_usize(v_i_2550_);
lean_dec(v_i_2550_);
v_stop_boxed_2553_ = lean_unbox_usize(v_stop_2551_);
lean_dec(v_stop_2551_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2548_, v_as_2549_, v_i_boxed_2552_, v_stop_boxed_2553_);
lean_dec_ref(v_as_2549_);
lean_dec_ref(v_a_2548_);
v_r_2555_ = lean_box(v_res_2554_);
return v_r_2555_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_as_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = lean_array_get_size(v_as_2556_);
v___x_2560_ = lean_nat_dec_lt(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
return v___x_2560_;
}
else
{
if (v___x_2560_ == 0)
{
return v___x_2560_;
}
else
{
size_t v___x_2561_; size_t v___x_2562_; uint8_t v___x_2563_; 
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = lean_usize_of_nat(v___x_2559_);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2557_, v_as_2556_, v___x_2561_, v___x_2562_);
return v___x_2563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_as_2564_, lean_object* v_a_2565_){
_start:
{
uint8_t v_res_2566_; lean_object* v_r_2567_; 
v_res_2566_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2564_, v_a_2565_);
lean_dec_ref(v_a_2565_);
lean_dec_ref(v_as_2564_);
v_r_2567_ = lean_box(v_res_2566_);
return v_r_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2570_, lean_object* v_tk_2571_, lean_object* v_c_2572_, lean_object* v_s_2573_){
_start:
{
if (lean_obj_tag(v_tk_2571_) == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v_c_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2575_ = lean_box(0);
v___x_2576_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2573_, v___x_2574_, v_startPos_2570_, v___x_2575_);
return v___x_2576_;
}
else
{
lean_object* v_toCacheableParserContext_2577_; lean_object* v_val_2578_; lean_object* v_toInputContext_2579_; lean_object* v_forbiddenTks_2580_; uint8_t v___x_2581_; 
v_toCacheableParserContext_2577_ = lean_ctor_get(v_c_2572_, 2);
v_val_2578_ = lean_ctor_get(v_tk_2571_, 0);
v_toInputContext_2579_ = lean_ctor_get(v_c_2572_, 0);
lean_inc_ref(v_toInputContext_2579_);
v_forbiddenTks_2580_ = lean_ctor_get(v_toCacheableParserContext_2577_, 3);
v___x_2581_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_2580_, v_val_2578_);
if (v___x_2581_ == 0)
{
lean_object* v_leading_2582_; lean_object* v___x_2583_; lean_object* v_stopPos_2584_; lean_object* v_s_2585_; lean_object* v_s_2586_; lean_object* v___y_2588_; lean_object* v_pos_2592_; lean_object* v_inputString_2593_; lean_object* v_endPos_2594_; uint8_t v___x_2595_; 
lean_inc(v_startPos_2570_);
v_leading_2582_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2572_, v_startPos_2570_);
v___x_2583_ = lean_string_utf8_byte_size(v_val_2578_);
v_stopPos_2584_ = lean_nat_add(v_startPos_2570_, v___x_2583_);
lean_inc(v_stopPos_2584_);
v_s_2585_ = l_Lean_Parser_ParserState_setPos(v_s_2573_, v_stopPos_2584_);
v_s_2586_ = l_Lean_Parser_whitespace(v_c_2572_, v_s_2585_);
v_pos_2592_ = lean_ctor_get(v_s_2586_, 2);
v_inputString_2593_ = lean_ctor_get(v_toInputContext_2579_, 0);
lean_inc_ref(v_inputString_2593_);
v_endPos_2594_ = lean_ctor_get(v_toInputContext_2579_, 3);
lean_inc(v_endPos_2594_);
lean_dec_ref(v_toInputContext_2579_);
v___x_2595_ = lean_nat_dec_le(v_pos_2592_, v_endPos_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_inc(v_stopPos_2584_);
v___x_2596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2596_, 0, v_inputString_2593_);
lean_ctor_set(v___x_2596_, 1, v_stopPos_2584_);
lean_ctor_set(v___x_2596_, 2, v_endPos_2594_);
v___y_2588_ = v___x_2596_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2597_; 
lean_dec(v_endPos_2594_);
lean_inc(v_pos_2592_);
lean_inc(v_stopPos_2584_);
v___x_2597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2597_, 0, v_inputString_2593_);
lean_ctor_set(v___x_2597_, 1, v_stopPos_2584_);
lean_ctor_set(v___x_2597_, 2, v_pos_2592_);
v___y_2588_ = v___x_2597_;
goto v___jp_2587_;
}
v___jp_2587_:
{
lean_object* v___x_2589_; lean_object* v_atom_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2589_, 0, v_leading_2582_);
lean_ctor_set(v___x_2589_, 1, v_startPos_2570_);
lean_ctor_set(v___x_2589_, 2, v___y_2588_);
lean_ctor_set(v___x_2589_, 3, v_stopPos_2584_);
lean_inc(v_val_2578_);
v_atom_2590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2590_, 0, v___x_2589_);
lean_ctor_set(v_atom_2590_, 1, v_val_2578_);
v___x_2591_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2586_, v_atom_2590_);
return v___x_2591_;
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_toInputContext_2579_);
lean_dec_ref(v_c_2572_);
v___x_2598_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2599_ = lean_box(0);
v___x_2600_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2573_, v___x_2598_, v_startPos_2570_, v___x_2599_);
return v___x_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2601_, lean_object* v_tk_2602_, lean_object* v_c_2603_, lean_object* v_s_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2601_, v_tk_2602_, v_c_2603_, v_s_2604_);
lean_dec(v_tk_2602_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2606_, lean_object* v_tk_2607_, lean_object* v_val_2608_, uint8_t v_includeWhitespace_2609_, lean_object* v_c_2610_, lean_object* v_s_2611_){
_start:
{
lean_object* v_pos_2612_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; uint8_t v___x_2622_; 
v_pos_2612_ = lean_ctor_get(v_s_2611_, 2);
v___x_2622_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2606_, v_pos_2612_, v_tk_2607_);
if (v___x_2622_ == 0)
{
lean_object* v_toInputContext_2623_; lean_object* v_inputString_2624_; lean_object* v_endPos_2625_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v_pos_2629_; lean_object* v___y_2635_; uint8_t v___x_2638_; 
lean_inc(v_pos_2612_);
v_toInputContext_2623_ = lean_ctor_get(v_c_2610_, 0);
v_inputString_2624_ = lean_ctor_get(v_toInputContext_2623_, 0);
lean_inc_ref(v_inputString_2624_);
v_endPos_2625_ = lean_ctor_get(v_toInputContext_2623_, 3);
lean_inc(v_endPos_2625_);
v___x_2638_ = lean_nat_dec_le(v_pos_2612_, v_endPos_2625_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; 
lean_inc(v_endPos_2625_);
lean_inc(v_startPos_2606_);
lean_inc_ref(v_inputString_2624_);
v___x_2639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2639_, 0, v_inputString_2624_);
lean_ctor_set(v___x_2639_, 1, v_startPos_2606_);
lean_ctor_set(v___x_2639_, 2, v_endPos_2625_);
v___y_2635_ = v___x_2639_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2640_; 
lean_inc(v_pos_2612_);
lean_inc(v_startPos_2606_);
lean_inc_ref(v_inputString_2624_);
v___x_2640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2640_, 0, v_inputString_2624_);
lean_ctor_set(v___x_2640_, 1, v_startPos_2606_);
lean_ctor_set(v___x_2640_, 2, v_pos_2612_);
v___y_2635_ = v___x_2640_;
goto v___jp_2634_;
}
v___jp_2626_:
{
lean_object* v_leading_2630_; uint8_t v___x_2631_; 
lean_inc(v_startPos_2606_);
v_leading_2630_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2610_, v_startPos_2606_);
lean_dec_ref(v_c_2610_);
v___x_2631_ = lean_nat_dec_le(v_pos_2629_, v_endPos_2625_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec(v_pos_2629_);
lean_inc(v_pos_2612_);
v___x_2632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2632_, 0, v_inputString_2624_);
lean_ctor_set(v___x_2632_, 1, v_pos_2612_);
lean_ctor_set(v___x_2632_, 2, v_endPos_2625_);
v___y_2614_ = v___y_2627_;
v___y_2615_ = v___y_2628_;
v___y_2616_ = v_leading_2630_;
v___y_2617_ = v___x_2632_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2633_; 
lean_dec(v_endPos_2625_);
lean_inc(v_pos_2612_);
v___x_2633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2633_, 0, v_inputString_2624_);
lean_ctor_set(v___x_2633_, 1, v_pos_2612_);
lean_ctor_set(v___x_2633_, 2, v_pos_2629_);
v___y_2614_ = v___y_2627_;
v___y_2615_ = v___y_2628_;
v___y_2616_ = v_leading_2630_;
v___y_2617_ = v___x_2633_;
goto v___jp_2613_;
}
}
v___jp_2634_:
{
if (v_includeWhitespace_2609_ == 0)
{
lean_inc(v_pos_2612_);
v___y_2627_ = v___y_2635_;
v___y_2628_ = v_s_2611_;
v_pos_2629_ = v_pos_2612_;
goto v___jp_2626_;
}
else
{
lean_object* v___x_2636_; lean_object* v_pos_2637_; 
lean_inc_ref(v_c_2610_);
v___x_2636_ = l_Lean_Parser_whitespace(v_c_2610_, v_s_2611_);
v_pos_2637_ = lean_ctor_get(v___x_2636_, 2);
lean_inc(v_pos_2637_);
v___y_2627_ = v___y_2635_;
v___y_2628_ = v___x_2636_;
v_pos_2629_ = v_pos_2637_;
goto v___jp_2626_;
}
}
}
else
{
lean_object* v___x_2641_; 
lean_dec(v_val_2608_);
v___x_2641_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2606_, v_tk_2607_, v_c_2610_, v_s_2611_);
return v___x_2641_;
}
v___jp_2613_:
{
lean_object* v_info_2618_; lean_object* v___x_2619_; lean_object* v_atom_2620_; lean_object* v___x_2621_; 
v_info_2618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2618_, 0, v___y_2616_);
lean_ctor_set(v_info_2618_, 1, v_startPos_2606_);
lean_ctor_set(v_info_2618_, 2, v___y_2617_);
lean_ctor_set(v_info_2618_, 3, v_pos_2612_);
v___x_2619_ = lean_box(0);
v_atom_2620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2620_, 0, v_info_2618_);
lean_ctor_set(v_atom_2620_, 1, v___y_2614_);
lean_ctor_set(v_atom_2620_, 2, v_val_2608_);
lean_ctor_set(v_atom_2620_, 3, v___x_2619_);
v___x_2621_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2615_, v_atom_2620_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2642_, lean_object* v_tk_2643_, lean_object* v_val_2644_, lean_object* v_includeWhitespace_2645_, lean_object* v_c_2646_, lean_object* v_s_2647_){
_start:
{
uint8_t v_includeWhitespace_boxed_2648_; lean_object* v_res_2649_; 
v_includeWhitespace_boxed_2648_ = lean_unbox(v_includeWhitespace_2645_);
v_res_2649_ = l_Lean_Parser_mkIdResult(v_startPos_2642_, v_tk_2643_, v_val_2644_, v_includeWhitespace_boxed_2648_, v_c_2646_, v_s_2647_);
lean_dec(v_tk_2643_);
return v_res_2649_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2650_){
_start:
{
uint32_t v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = 65;
v___x_2673_ = lean_uint32_dec_le(v___x_2672_, v___y_2650_);
if (v___x_2673_ == 0)
{
goto v___jp_2667_;
}
else
{
uint32_t v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = 90;
v___x_2675_ = lean_uint32_dec_le(v___y_2650_, v___x_2674_);
if (v___x_2675_ == 0)
{
goto v___jp_2667_;
}
else
{
return v___x_2675_;
}
}
v___jp_2651_:
{
uint32_t v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = 95;
v___x_2653_ = lean_uint32_dec_eq(v___y_2650_, v___x_2652_);
if (v___x_2653_ == 0)
{
uint32_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = 39;
v___x_2655_ = lean_uint32_dec_eq(v___y_2650_, v___x_2654_);
if (v___x_2655_ == 0)
{
uint32_t v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = 33;
v___x_2657_ = lean_uint32_dec_eq(v___y_2650_, v___x_2656_);
if (v___x_2657_ == 0)
{
uint32_t v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = 63;
v___x_2659_ = lean_uint32_dec_eq(v___y_2650_, v___x_2658_);
if (v___x_2659_ == 0)
{
uint8_t v___x_2660_; 
v___x_2660_ = l_Lean_isLetterLike(v___y_2650_);
if (v___x_2660_ == 0)
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_isSubScriptAlnum(v___y_2650_);
return v___x_2661_;
}
else
{
return v___x_2660_;
}
}
else
{
return v___x_2659_;
}
}
else
{
return v___x_2657_;
}
}
else
{
return v___x_2655_;
}
}
else
{
return v___x_2653_;
}
}
v___jp_2662_:
{
uint32_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = 48;
v___x_2664_ = lean_uint32_dec_le(v___x_2663_, v___y_2650_);
if (v___x_2664_ == 0)
{
goto v___jp_2651_;
}
else
{
uint32_t v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = 57;
v___x_2666_ = lean_uint32_dec_le(v___y_2650_, v___x_2665_);
if (v___x_2666_ == 0)
{
goto v___jp_2651_;
}
else
{
return v___x_2666_;
}
}
}
v___jp_2667_:
{
uint32_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = 97;
v___x_2669_ = lean_uint32_dec_le(v___x_2668_, v___y_2650_);
if (v___x_2669_ == 0)
{
goto v___jp_2662_;
}
else
{
uint32_t v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = 122;
v___x_2671_ = lean_uint32_dec_le(v___y_2650_, v___x_2670_);
if (v___x_2671_ == 0)
{
goto v___jp_2662_;
}
else
{
return v___x_2671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2676_){
_start:
{
uint32_t v___y_274__boxed_2677_; uint8_t v_res_2678_; lean_object* v_r_2679_; 
v___y_274__boxed_2677_ = lean_unbox_uint32(v___y_2676_);
lean_dec(v___y_2676_);
v_res_2678_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_274__boxed_2677_);
v_r_2679_ = lean_box(v_res_2678_);
return v_r_2679_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2680_){
_start:
{
uint32_t v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = l_Lean_idEndEscape;
v___x_2682_ = lean_uint32_dec_eq(v___y_2680_, v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2683_){
_start:
{
uint32_t v___y_327__boxed_2684_; uint8_t v_res_2685_; lean_object* v_r_2686_; 
v___y_327__boxed_2684_ = lean_unbox_uint32(v___y_2683_);
lean_dec(v___y_2683_);
v_res_2685_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_327__boxed_2684_);
v_r_2686_ = lean_box(v_res_2685_);
return v_r_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2690_, lean_object* v_tk_2691_, uint8_t v_includeWhitespace_2692_, lean_object* v_r_2693_, lean_object* v_c_2694_, lean_object* v_s_2695_){
_start:
{
lean_object* v_pos_2696_; lean_object* v_toInputContext_2697_; uint8_t v___x_2698_; 
v_pos_2696_ = lean_ctor_get(v_s_2695_, 2);
v_toInputContext_2697_ = lean_ctor_get(v_c_2694_, 0);
v___x_2698_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2697_, v_pos_2696_);
if (v___x_2698_ == 0)
{
lean_object* v_inputString_2699_; uint32_t v_curr_2700_; uint32_t v___x_2701_; uint8_t v___x_2702_; 
v_inputString_2699_ = lean_ctor_get(v_toInputContext_2697_, 0);
v_curr_2700_ = lean_string_utf8_get_fast(v_inputString_2699_, v_pos_2696_);
v___x_2701_ = l_Lean_idBeginEscape;
v___x_2702_ = lean_uint32_dec_eq(v_curr_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___f_2703_; uint32_t v___x_2724_; uint8_t v___x_2725_; 
v___f_2703_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2724_ = 65;
v___x_2725_ = lean_uint32_dec_le(v___x_2724_, v_curr_2700_);
if (v___x_2725_ == 0)
{
goto v___jp_2719_;
}
else
{
uint32_t v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = 90;
v___x_2727_ = lean_uint32_dec_le(v_curr_2700_, v___x_2726_);
if (v___x_2727_ == 0)
{
goto v___jp_2719_;
}
else
{
lean_inc(v_pos_2696_);
goto v___jp_2704_;
}
}
v___jp_2704_:
{
lean_object* v___x_2705_; lean_object* v_s_2706_; lean_object* v_pos_2707_; lean_object* v___x_2708_; lean_object* v_r_2709_; uint8_t v___x_2710_; 
v___x_2705_ = l_Lean_Parser_ParserState_next(v_s_2695_, v_c_2694_, v_pos_2696_);
v_s_2706_ = l_Lean_Parser_takeWhileFn(v___f_2703_, v_c_2694_, v___x_2705_);
v_pos_2707_ = lean_ctor_get(v_s_2706_, 2);
v___x_2708_ = lean_string_utf8_extract(v_inputString_2699_, v_pos_2696_, v_pos_2707_);
lean_dec(v_pos_2696_);
v_r_2709_ = l_Lean_Name_str___override(v_r_2693_, v___x_2708_);
v___x_2710_ = l_Lean_Parser_isIdCont(v_c_2694_, v_s_2706_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Parser_mkIdResult(v_startPos_2690_, v_tk_2691_, v_r_2709_, v_includeWhitespace_2692_, v_c_2694_, v_s_2706_);
return v___x_2711_;
}
else
{
lean_object* v_s_2712_; 
lean_inc(v_pos_2707_);
v_s_2712_ = l_Lean_Parser_ParserState_next(v_s_2706_, v_c_2694_, v_pos_2707_);
lean_dec(v_pos_2707_);
v_r_2693_ = v_r_2709_;
v_s_2695_ = v_s_2712_;
goto _start;
}
}
v___jp_2714_:
{
uint32_t v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = 95;
v___x_2716_ = lean_uint32_dec_eq(v_curr_2700_, v___x_2715_);
if (v___x_2716_ == 0)
{
uint8_t v___x_2717_; 
v___x_2717_ = l_Lean_isLetterLike(v_curr_2700_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_dec(v_r_2693_);
v___x_2718_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2690_, v_tk_2691_, v_c_2694_, v_s_2695_);
return v___x_2718_;
}
else
{
lean_inc(v_pos_2696_);
goto v___jp_2704_;
}
}
else
{
lean_inc(v_pos_2696_);
goto v___jp_2704_;
}
}
v___jp_2719_:
{
uint32_t v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = 97;
v___x_2721_ = lean_uint32_dec_le(v___x_2720_, v_curr_2700_);
if (v___x_2721_ == 0)
{
goto v___jp_2714_;
}
else
{
uint32_t v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = 122;
v___x_2723_ = lean_uint32_dec_le(v_curr_2700_, v___x_2722_);
if (v___x_2723_ == 0)
{
goto v___jp_2714_;
}
else
{
lean_inc(v_pos_2696_);
goto v___jp_2704_;
}
}
}
}
else
{
lean_object* v___f_2728_; lean_object* v_startPart_2729_; lean_object* v___x_2730_; lean_object* v_s_2731_; lean_object* v_pos_2732_; uint8_t v___x_2733_; 
v___f_2728_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2729_ = lean_string_utf8_next_fast(v_inputString_2699_, v_pos_2696_);
v___x_2730_ = l_Lean_Parser_ParserState_setPos(v_s_2695_, v_startPart_2729_);
v_s_2731_ = l_Lean_Parser_takeUntilFn(v___f_2728_, v_c_2694_, v___x_2730_);
v_pos_2732_ = lean_ctor_get(v_s_2731_, 2);
v___x_2733_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2697_, v_pos_2732_);
if (v___x_2733_ == 0)
{
lean_object* v_s_2734_; lean_object* v___x_2735_; lean_object* v_r_2736_; uint8_t v___x_2737_; 
lean_inc(v_pos_2732_);
v_s_2734_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2731_, v_c_2694_, v_pos_2732_);
v___x_2735_ = lean_string_utf8_extract(v_inputString_2699_, v_startPart_2729_, v_pos_2732_);
lean_dec(v_pos_2732_);
v_r_2736_ = l_Lean_Name_str___override(v_r_2693_, v___x_2735_);
v___x_2737_ = l_Lean_Parser_isIdCont(v_c_2694_, v_s_2734_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_Parser_mkIdResult(v_startPos_2690_, v_tk_2691_, v_r_2736_, v_includeWhitespace_2692_, v_c_2694_, v_s_2734_);
return v___x_2738_;
}
else
{
lean_object* v_pos_2739_; lean_object* v_s_2740_; 
v_pos_2739_ = lean_ctor_get(v_s_2734_, 2);
lean_inc(v_pos_2739_);
v_s_2740_ = l_Lean_Parser_ParserState_next(v_s_2734_, v_c_2694_, v_pos_2739_);
lean_dec(v_pos_2739_);
v_r_2693_ = v_r_2736_;
v_s_2695_ = v_s_2740_;
goto _start;
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec_ref(v_c_2694_);
lean_dec(v_r_2693_);
lean_dec(v_startPos_2690_);
v___x_2742_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2743_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2731_, v___x_2742_, v_startPart_2729_);
return v___x_2743_;
}
}
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_c_2694_);
lean_dec(v_r_2693_);
lean_dec(v_startPos_2690_);
v___x_2744_ = lean_box(0);
v___x_2745_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2695_, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2746_, lean_object* v_tk_2747_, lean_object* v_includeWhitespace_2748_, lean_object* v_r_2749_, lean_object* v_c_2750_, lean_object* v_s_2751_){
_start:
{
uint8_t v_includeWhitespace_boxed_2752_; lean_object* v_res_2753_; 
v_includeWhitespace_boxed_2752_ = lean_unbox(v_includeWhitespace_2748_);
v_res_2753_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2746_, v_tk_2747_, v_includeWhitespace_boxed_2752_, v_r_2749_, v_c_2750_, v_s_2751_);
lean_dec(v_tk_2747_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2754_, lean_object* v_tk_2755_, lean_object* v_r_2756_, uint8_t v_includeWhitespace_2757_, lean_object* v_c_2758_, lean_object* v_s_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2754_, v_tk_2755_, v_includeWhitespace_2757_, v_r_2756_, v_c_2758_, v_s_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2761_, lean_object* v_tk_2762_, lean_object* v_r_2763_, lean_object* v_includeWhitespace_2764_, lean_object* v_c_2765_, lean_object* v_s_2766_){
_start:
{
uint8_t v_includeWhitespace_boxed_2767_; lean_object* v_res_2768_; 
v_includeWhitespace_boxed_2767_ = lean_unbox(v_includeWhitespace_2764_);
v_res_2768_ = l_Lean_Parser_identFnAux(v_startPos_2761_, v_tk_2762_, v_r_2763_, v_includeWhitespace_boxed_2767_, v_c_2765_, v_s_2766_);
lean_dec(v_tk_2762_);
return v_res_2768_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2769_){
_start:
{
uint32_t v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = 65;
v___x_2782_ = lean_uint32_dec_le(v___x_2781_, v_c_2769_);
if (v___x_2782_ == 0)
{
goto v___jp_2776_;
}
else
{
uint32_t v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = 90;
v___x_2784_ = lean_uint32_dec_le(v_c_2769_, v___x_2783_);
if (v___x_2784_ == 0)
{
goto v___jp_2776_;
}
else
{
return v___x_2784_;
}
}
v___jp_2770_:
{
uint32_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = 95;
v___x_2772_ = lean_uint32_dec_eq(v_c_2769_, v___x_2771_);
if (v___x_2772_ == 0)
{
uint8_t v___x_2773_; 
v___x_2773_ = l_Lean_isLetterLike(v_c_2769_);
if (v___x_2773_ == 0)
{
uint32_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = l_Lean_idBeginEscape;
v___x_2775_ = lean_uint32_dec_eq(v_c_2769_, v___x_2774_);
return v___x_2775_;
}
else
{
return v___x_2773_;
}
}
else
{
return v___x_2772_;
}
}
v___jp_2776_:
{
uint32_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = 97;
v___x_2778_ = lean_uint32_dec_le(v___x_2777_, v_c_2769_);
if (v___x_2778_ == 0)
{
goto v___jp_2770_;
}
else
{
uint32_t v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = 122;
v___x_2780_ = lean_uint32_dec_le(v_c_2769_, v___x_2779_);
if (v___x_2780_ == 0)
{
goto v___jp_2770_;
}
else
{
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2785_){
_start:
{
uint32_t v_c_boxed_2786_; uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_c_boxed_2786_ = lean_unbox_uint32(v_c_2785_);
lean_dec(v_c_2785_);
v_res_2787_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2786_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2790_, lean_object* v_c_2791_, lean_object* v_s_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v_s_2797_; lean_object* v_stxStack_2798_; lean_object* v_errorMsg_2799_; uint8_t v___x_2800_; 
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_box(0);
v___x_2795_ = 1;
v___x_2796_ = l_Lean_Parser_ParserState_next(v_s_2792_, v_c_2791_, v_startPos_2790_);
v_s_2797_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2790_, v___x_2793_, v___x_2795_, v___x_2794_, v_c_2791_, v___x_2796_);
v_stxStack_2798_ = lean_ctor_get(v_s_2797_, 0);
v_errorMsg_2799_ = lean_ctor_get(v_s_2797_, 4);
v___x_2800_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2799_, v___x_2793_);
if (v___x_2800_ == 0)
{
return v_s_2797_;
}
else
{
lean_object* v_stx_2801_; 
v_stx_2801_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2798_);
if (lean_obj_tag(v_stx_2801_) == 3)
{
lean_object* v_rawVal_2802_; lean_object* v_info_2803_; lean_object* v_str_2804_; lean_object* v_startPos_2805_; lean_object* v_stopPos_2806_; lean_object* v_s_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_rawVal_2802_ = lean_ctor_get(v_stx_2801_, 1);
lean_inc_ref(v_rawVal_2802_);
v_info_2803_ = lean_ctor_get(v_stx_2801_, 0);
lean_inc(v_info_2803_);
lean_dec_ref_known(v_stx_2801_, 4);
v_str_2804_ = lean_ctor_get(v_rawVal_2802_, 0);
lean_inc_ref(v_str_2804_);
v_startPos_2805_ = lean_ctor_get(v_rawVal_2802_, 1);
lean_inc(v_startPos_2805_);
v_stopPos_2806_ = lean_ctor_get(v_rawVal_2802_, 2);
lean_inc(v_stopPos_2806_);
lean_dec_ref(v_rawVal_2802_);
v_s_2807_ = l_Lean_Parser_ParserState_popSyntax(v_s_2797_);
v___x_2808_ = lean_string_utf8_extract(v_str_2804_, v_startPos_2805_, v_stopPos_2806_);
lean_dec(v_stopPos_2806_);
lean_dec(v_startPos_2805_);
lean_dec_ref(v_str_2804_);
v___x_2809_ = l_Lean_Syntax_mkNameLit(v___x_2808_, v_info_2803_);
v___x_2810_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2807_, v___x_2809_);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec(v_stx_2801_);
v___x_2811_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2812_ = l_Lean_Parser_ParserState_mkError(v_s_2797_, v___x_2811_);
return v___x_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2813_, lean_object* v_s_2814_){
_start:
{
lean_object* v_toInputContext_2815_; lean_object* v_pos_2816_; lean_object* v_tokens_2817_; lean_object* v_inputString_2818_; lean_object* v_endPos_2819_; uint32_t v_curr_2820_; uint32_t v___x_2821_; uint8_t v___x_2822_; uint8_t v___x_2823_; 
v_toInputContext_2815_ = lean_ctor_get(v_c_2813_, 0);
v_pos_2816_ = lean_ctor_get(v_s_2814_, 2);
v_tokens_2817_ = lean_ctor_get(v_c_2813_, 3);
v_inputString_2818_ = lean_ctor_get(v_toInputContext_2815_, 0);
v_endPos_2819_ = lean_ctor_get(v_toInputContext_2815_, 3);
v_curr_2820_ = lean_string_utf8_get(v_inputString_2818_, v_pos_2816_);
v___x_2821_ = 34;
v___x_2822_ = lean_uint32_dec_eq(v_curr_2820_, v___x_2821_);
v___x_2823_ = 1;
if (v___x_2822_ == 0)
{
uint32_t v___x_2848_; uint8_t v___x_2849_; 
v___x_2848_ = 39;
v___x_2849_ = lean_uint32_dec_eq(v_curr_2820_, v___x_2848_);
if (v___x_2849_ == 0)
{
goto v___jp_2842_;
}
else
{
lean_object* v___x_2850_; uint32_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_string_utf8_next(v_inputString_2818_, v_pos_2816_);
v___x_2851_ = lean_string_utf8_get(v_inputString_2818_, v___x_2850_);
lean_dec(v___x_2850_);
v___x_2852_ = lean_uint32_dec_eq(v___x_2851_, v___x_2848_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_inc(v_pos_2816_);
v___x_2853_ = l_Lean_Parser_ParserState_next(v_s_2814_, v_c_2813_, v_pos_2816_);
v___x_2854_ = l_Lean_Parser_charLitFnAux(v_pos_2816_, v_c_2813_, v___x_2853_);
return v___x_2854_;
}
else
{
goto v___jp_2842_;
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_inc(v_pos_2816_);
v___x_2855_ = l_Lean_Parser_ParserState_next(v_s_2814_, v_c_2813_, v_pos_2816_);
v___x_2856_ = l_Lean_Parser_strLitFnAux(v_pos_2816_, v___x_2823_, v_c_2813_, v___x_2855_);
return v___x_2856_;
}
v___jp_2824_:
{
lean_object* v_tk_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_inc(v_pos_2816_);
v_tk_2825_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2818_, v_tokens_2817_, v_pos_2816_, v_endPos_2819_);
v___x_2826_ = lean_box(0);
v___x_2827_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2816_, v_tk_2825_, v___x_2823_, v___x_2826_, v_c_2813_, v_s_2814_);
lean_dec(v_tk_2825_);
return v___x_2827_;
}
v___jp_2828_:
{
uint32_t v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = 114;
v___x_2830_ = lean_uint32_dec_eq(v_curr_2820_, v___x_2829_);
if (v___x_2830_ == 0)
{
goto v___jp_2824_;
}
else
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_string_utf8_next(v_inputString_2818_, v_pos_2816_);
v___x_2832_ = l_Lean_Parser_isRawStrLitStart(v_c_2813_, v___x_2831_);
if (v___x_2832_ == 0)
{
goto v___jp_2824_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = l_Lean_Parser_ParserState_next(v_s_2814_, v_c_2813_, v_pos_2816_);
v___x_2834_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2816_, v_c_2813_, v___x_2833_);
return v___x_2834_;
}
}
}
v___jp_2835_:
{
uint32_t v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = 96;
v___x_2837_ = lean_uint32_dec_eq(v_curr_2820_, v___x_2836_);
if (v___x_2837_ == 0)
{
goto v___jp_2828_;
}
else
{
lean_object* v___x_2838_; uint32_t v___x_2839_; uint8_t v___x_2840_; 
v___x_2838_ = lean_string_utf8_next(v_inputString_2818_, v_pos_2816_);
v___x_2839_ = lean_string_utf8_get(v_inputString_2818_, v___x_2838_);
lean_dec(v___x_2838_);
v___x_2840_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2839_);
if (v___x_2840_ == 0)
{
goto v___jp_2828_;
}
else
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2816_, v_c_2813_, v_s_2814_);
return v___x_2841_;
}
}
}
v___jp_2842_:
{
uint32_t v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = 48;
v___x_2844_ = lean_uint32_dec_le(v___x_2843_, v_curr_2820_);
if (v___x_2844_ == 0)
{
lean_inc(v_pos_2816_);
goto v___jp_2835_;
}
else
{
uint32_t v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = 57;
v___x_2846_ = lean_uint32_dec_le(v_curr_2820_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_inc(v_pos_2816_);
goto v___jp_2835_;
}
else
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_Parser_numberFnAux(v___x_2823_, v_c_2813_, v_s_2814_);
return v___x_2847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2857_, lean_object* v_s_2858_){
_start:
{
lean_object* v_cache_2859_; lean_object* v_errorMsg_2860_; 
v_cache_2859_ = lean_ctor_get(v_s_2858_, 3);
lean_inc_ref(v_cache_2859_);
v_errorMsg_2860_ = lean_ctor_get(v_s_2858_, 4);
if (lean_obj_tag(v_errorMsg_2860_) == 0)
{
lean_object* v_stxStack_2861_; lean_object* v_lhsPrec_2862_; lean_object* v_pos_2863_; lean_object* v_recoveredErrors_2864_; lean_object* v_parserCache_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2890_; 
v_stxStack_2861_ = lean_ctor_get(v_s_2858_, 0);
v_lhsPrec_2862_ = lean_ctor_get(v_s_2858_, 1);
v_pos_2863_ = lean_ctor_get(v_s_2858_, 2);
v_recoveredErrors_2864_ = lean_ctor_get(v_s_2858_, 5);
v_parserCache_2865_ = lean_ctor_get(v_cache_2859_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_cache_2859_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; 
v_unused_2891_ = lean_ctor_get(v_cache_2859_, 0);
lean_dec(v_unused_2891_);
v___x_2867_ = v_cache_2859_;
v_isShared_2868_ = v_isSharedCheck_2890_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_parserCache_2865_);
lean_dec(v_cache_2859_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2890_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2869_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2861_);
v___x_2870_ = lean_unsigned_to_nat(0u);
v___x_2871_ = lean_nat_dec_eq(v___x_2869_, v___x_2870_);
lean_dec(v___x_2869_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2883_; 
lean_inc_ref(v_recoveredErrors_2864_);
lean_inc(v_pos_2863_);
lean_inc(v_lhsPrec_2862_);
lean_inc_ref(v_stxStack_2861_);
lean_inc(v_errorMsg_2860_);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_s_2858_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; lean_object* v_unused_2885_; lean_object* v_unused_2886_; lean_object* v_unused_2887_; lean_object* v_unused_2888_; lean_object* v_unused_2889_; 
v_unused_2884_ = lean_ctor_get(v_s_2858_, 5);
lean_dec(v_unused_2884_);
v_unused_2885_ = lean_ctor_get(v_s_2858_, 4);
lean_dec(v_unused_2885_);
v_unused_2886_ = lean_ctor_get(v_s_2858_, 3);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v_s_2858_, 2);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_s_2858_, 1);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_s_2858_, 0);
lean_dec(v_unused_2889_);
v___x_2873_ = v_s_2858_;
v_isShared_2874_ = v_isSharedCheck_2883_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v_s_2858_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2883_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v_tk_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v_tk_2875_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2861_);
lean_inc(v_pos_2863_);
v___x_2876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2876_, 0, v_startPos_2857_);
lean_ctor_set(v___x_2876_, 1, v_pos_2863_);
lean_ctor_set(v___x_2876_, 2, v_tk_2875_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2876_);
v___x_2878_ = v___x_2867_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_parserCache_2865_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 3, v___x_2878_);
v___x_2880_ = v___x_2873_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_stxStack_2861_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_lhsPrec_2862_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_pos_2863_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_errorMsg_2860_);
lean_ctor_set(v_reuseFailAlloc_2881_, 5, v_recoveredErrors_2864_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_del_object(v___x_2867_);
lean_dec_ref(v_parserCache_2865_);
lean_dec(v_startPos_2857_);
return v_s_2858_;
}
}
}
else
{
lean_dec_ref(v_cache_2859_);
lean_dec(v_startPos_2857_);
return v_s_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2892_, lean_object* v_c_2893_, lean_object* v_s_2894_){
_start:
{
lean_object* v_pos_2895_; lean_object* v_cache_2896_; lean_object* v_toInputContext_2897_; uint8_t v___x_2898_; 
v_pos_2895_ = lean_ctor_get(v_s_2894_, 2);
v_cache_2896_ = lean_ctor_get(v_s_2894_, 3);
v_toInputContext_2897_ = lean_ctor_get(v_c_2893_, 0);
v___x_2898_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2897_, v_pos_2895_);
if (v___x_2898_ == 0)
{
lean_object* v_tokenCache_2899_; lean_object* v_startPos_2900_; lean_object* v_stopPos_2901_; lean_object* v_token_2902_; uint8_t v_decide_2903_; 
lean_dec(v_expected_2892_);
v_tokenCache_2899_ = lean_ctor_get(v_cache_2896_, 0);
v_startPos_2900_ = lean_ctor_get(v_tokenCache_2899_, 0);
v_stopPos_2901_ = lean_ctor_get(v_tokenCache_2899_, 1);
v_token_2902_ = lean_ctor_get(v_tokenCache_2899_, 2);
v_decide_2903_ = lean_nat_dec_eq(v_startPos_2900_, v_pos_2895_);
if (v_decide_2903_ == 0)
{
lean_object* v_s_2904_; lean_object* v___x_2905_; 
lean_inc(v_pos_2895_);
v_s_2904_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2893_, v_s_2894_);
v___x_2905_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2895_, v_s_2904_);
return v___x_2905_;
}
else
{
lean_object* v_s_2906_; lean_object* v___x_2907_; 
lean_inc(v_token_2902_);
lean_inc(v_stopPos_2901_);
lean_dec_ref(v_c_2893_);
v_s_2906_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2894_, v_token_2902_);
v___x_2907_ = l_Lean_Parser_ParserState_setPos(v_s_2906_, v_stopPos_2901_);
return v___x_2907_;
}
}
else
{
lean_object* v___x_2908_; 
lean_dec_ref(v_c_2893_);
v___x_2908_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2894_, v_expected_2892_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2909_, lean_object* v_s_2910_){
_start:
{
lean_object* v_pos_2911_; lean_object* v_iniSz_2912_; lean_object* v___x_2913_; lean_object* v_s_2914_; lean_object* v_errorMsg_2915_; 
v_pos_2911_ = lean_ctor_get(v_s_2910_, 2);
lean_inc(v_pos_2911_);
v_iniSz_2912_ = l_Lean_Parser_ParserState_stackSize(v_s_2910_);
v___x_2913_ = lean_box(0);
v_s_2914_ = l_Lean_Parser_tokenFn(v___x_2913_, v_c_2909_, v_s_2910_);
v_errorMsg_2915_ = lean_ctor_get(v_s_2914_, 4);
lean_inc(v_errorMsg_2915_);
if (lean_obj_tag(v_errorMsg_2915_) == 1)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2924_; 
v_isSharedCheck_2924_ = !lean_is_exclusive(v_errorMsg_2915_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; 
v_unused_2925_ = lean_ctor_get(v_errorMsg_2915_, 0);
lean_dec(v_unused_2925_);
v___x_2917_ = v_errorMsg_2915_;
v_isShared_2918_ = v_isSharedCheck_2924_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v_errorMsg_2915_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2924_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_inc_ref(v_s_2914_);
v___x_2919_ = l_Lean_Parser_ParserState_restore(v_s_2914_, v_iniSz_2912_, v_pos_2911_);
lean_dec(v_iniSz_2912_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set_tag(v___x_2917_, 0);
lean_ctor_set(v___x_2917_, 0, v_s_2914_);
v___x_2921_ = v___x_2917_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_s_2914_);
v___x_2921_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2919_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
return v___x_2922_;
}
}
}
else
{
lean_object* v_stxStack_2926_; lean_object* v_stx_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v_errorMsg_2915_);
v_stxStack_2926_ = lean_ctor_get(v_s_2914_, 0);
v_stx_2927_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2926_);
v___x_2928_ = l_Lean_Parser_ParserState_restore(v_s_2914_, v_iniSz_2912_, v_pos_2911_);
lean_dec(v_iniSz_2912_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_stx_2927_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2931_, lean_object* v_s_2932_){
_start:
{
lean_object* v_cache_2933_; lean_object* v_tokenCache_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2947_; 
v_cache_2933_ = lean_ctor_get(v_s_2932_, 3);
lean_inc_ref(v_cache_2933_);
v_tokenCache_2934_ = lean_ctor_get(v_cache_2933_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_cache_2933_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; 
v_unused_2948_ = lean_ctor_get(v_cache_2933_, 1);
lean_dec(v_unused_2948_);
v___x_2936_ = v_cache_2933_;
v_isShared_2937_ = v_isSharedCheck_2947_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_tokenCache_2934_);
lean_dec(v_cache_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2947_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_pos_2938_; lean_object* v_startPos_2939_; lean_object* v_token_2940_; uint8_t v_decide_2941_; 
v_pos_2938_ = lean_ctor_get(v_s_2932_, 2);
v_startPos_2939_ = lean_ctor_get(v_tokenCache_2934_, 0);
lean_inc(v_startPos_2939_);
v_token_2940_ = lean_ctor_get(v_tokenCache_2934_, 2);
lean_inc(v_token_2940_);
lean_dec_ref(v_tokenCache_2934_);
v_decide_2941_ = lean_nat_dec_eq(v_startPos_2939_, v_pos_2938_);
lean_dec(v_startPos_2939_);
if (v_decide_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec(v_token_2940_);
lean_del_object(v___x_2936_);
v___x_2942_ = l_Lean_Parser_peekTokenAux(v_c_2931_, v_s_2932_);
return v___x_2942_;
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
lean_dec_ref(v_c_2931_);
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_token_2940_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v___x_2943_);
lean_ctor_set(v___x_2936_, 0, v_s_2932_);
v___x_2945_ = v___x_2936_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_s_2932_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2949_, lean_object* v_c_2950_, lean_object* v_s_2951_){
_start:
{
lean_object* v_pos_2952_; lean_object* v_toInputContext_2953_; uint8_t v___x_2954_; 
v_pos_2952_ = lean_ctor_get(v_s_2951_, 2);
v_toInputContext_2953_ = lean_ctor_get(v_c_2950_, 0);
v___x_2954_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2953_, v_pos_2952_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_inc(v_pos_2952_);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_box(0);
v___x_2957_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2952_, v___x_2955_, v_includeWhitespace_2949_, v___x_2956_, v_c_2950_, v_s_2951_);
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec_ref(v_c_2950_);
v___x_2958_ = lean_box(0);
v___x_2959_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2951_, v___x_2958_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2960_, lean_object* v_c_2961_, lean_object* v_s_2962_){
_start:
{
uint8_t v_includeWhitespace_boxed_2963_; lean_object* v_res_2964_; 
v_includeWhitespace_boxed_2963_ = lean_unbox(v_includeWhitespace_2960_);
v_res_2964_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2963_, v_c_2961_, v_s_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_2965_, lean_object* v_expected_2966_, lean_object* v_c_2967_, lean_object* v_s_2968_){
_start:
{
lean_object* v_pos_2969_; lean_object* v_s_2970_; lean_object* v_stxStack_2971_; lean_object* v_errorMsg_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v_pos_2969_ = lean_ctor_get(v_s_2968_, 2);
lean_inc(v_pos_2969_);
lean_inc(v_expected_2966_);
v_s_2970_ = l_Lean_Parser_tokenFn(v_expected_2966_, v_c_2967_, v_s_2968_);
v_stxStack_2971_ = lean_ctor_get(v_s_2970_, 0);
v_errorMsg_2972_ = lean_ctor_get(v_s_2970_, 4);
v___x_2973_ = lean_box(0);
v___x_2974_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v_pos_2969_);
lean_dec(v_expected_2966_);
lean_dec_ref(v_p_2965_);
return v_s_2970_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2971_);
if (lean_obj_tag(v___x_2975_) == 2)
{
lean_object* v_val_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_val_2976_ = lean_ctor_get(v___x_2975_, 1);
lean_inc_ref(v_val_2976_);
lean_dec_ref_known(v___x_2975_, 2);
v___x_2977_ = lean_apply_1(v_p_2965_, v_val_2976_);
v___x_2978_ = lean_unbox(v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2970_, v_expected_2966_, v_pos_2969_);
return v___x_2979_;
}
else
{
lean_dec(v_pos_2969_);
lean_dec(v_expected_2966_);
return v_s_2970_;
}
}
else
{
lean_object* v___x_2980_; 
lean_dec(v___x_2975_);
lean_dec_ref(v_p_2965_);
v___x_2980_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2970_, v_expected_2966_, v_pos_2969_);
return v___x_2980_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_2981_, lean_object* v_s_2982_){
_start:
{
uint8_t v___x_2983_; 
v___x_2983_ = lean_string_dec_eq(v_s_2982_, v_sym_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_2984_, lean_object* v_s_2985_){
_start:
{
uint8_t v_res_2986_; lean_object* v_r_2987_; 
v_res_2986_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_2984_, v_s_2985_);
lean_dec_ref(v_s_2985_);
lean_dec_ref(v_sym_2984_);
v_r_2987_ = lean_box(v_res_2986_);
return v_r_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_2988_, lean_object* v_errorMsg_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v___f_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2992_, 0, v_sym_2988_);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_errorMsg_2989_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l_Lean_Parser_satisfySymbolFn(v___f_2992_, v___x_2994_, v_a_2990_, v_a_2991_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_2996_, lean_object* v_tks_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_sym_2996_);
lean_ctor_set(v___x_2998_, 1, v_tks_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_2999_){
_start:
{
lean_object* v___f_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_inc_ref(v_sym_2999_);
v___f_3000_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3000_, 0, v_sym_2999_);
v___f_3001_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v_sym_2999_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3005_, 0, v___f_3000_);
lean_ctor_set(v___x_3005_, 1, v___f_3001_);
lean_ctor_set(v___x_3005_, 2, v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3010_ = lean_string_append(v___x_3009_, v_sym_3006_);
v___x_3011_ = lean_string_append(v___x_3010_, v___x_3009_);
v___x_3012_ = l_Lean_Parser_symbolFnAux(v_sym_3006_, v___x_3011_, v_a_3007_, v_a_3008_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v_str_3018_; lean_object* v_startInclusive_3019_; lean_object* v_endExclusive_3020_; lean_object* v_sym_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_string_utf8_byte_size(v_sym_3013_);
v___x_3016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3016_, 0, v_sym_3013_);
lean_ctor_set(v___x_3016_, 1, v___x_3014_);
lean_ctor_set(v___x_3016_, 2, v___x_3015_);
v___x_3017_ = l_String_Slice_trimAscii(v___x_3016_);
v_str_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_str_3018_);
v_startInclusive_3019_ = lean_ctor_get(v___x_3017_, 1);
lean_inc(v_startInclusive_3019_);
v_endExclusive_3020_ = lean_ctor_get(v___x_3017_, 2);
lean_inc(v_endExclusive_3020_);
lean_dec_ref(v___x_3017_);
v_sym_3021_ = lean_string_utf8_extract_fast(v_str_3018_, v_startInclusive_3019_, v_endExclusive_3020_);
lean_dec(v_endExclusive_3020_);
lean_dec(v_startInclusive_3019_);
lean_dec_ref(v_str_3018_);
lean_inc_ref(v_sym_3021_);
v___x_3022_ = l_Lean_Parser_symbolInfo(v_sym_3021_);
v___x_3023_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3023_, 0, v_sym_3021_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3025_, lean_object* v_errorMsg_3026_, lean_object* v_c_3027_, lean_object* v_s_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v_s_3031_; lean_object* v_stxStack_3035_; lean_object* v_errorMsg_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3029_ = lean_box(0);
lean_inc_ref(v_errorMsg_3026_);
v___x_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_errorMsg_3026_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v_s_3031_ = l_Lean_Parser_tokenFn(v___x_3030_, v_c_3027_, v_s_3028_);
v_stxStack_3035_ = lean_ctor_get(v_s_3031_, 0);
v_errorMsg_3036_ = lean_ctor_get(v_s_3031_, 4);
v___x_3037_ = lean_box(0);
v___x_3038_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3036_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_dec_ref(v_errorMsg_3026_);
lean_dec_ref(v_sym_3025_);
return v_s_3031_;
}
else
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3035_);
switch(lean_obj_tag(v___x_3039_))
{
case 2:
{
lean_object* v_val_3040_; uint8_t v___x_3041_; 
v_val_3040_ = lean_ctor_get(v___x_3039_, 1);
lean_inc_ref(v_val_3040_);
lean_dec_ref_known(v___x_3039_, 2);
v___x_3041_ = lean_string_dec_eq(v_sym_3025_, v_val_3040_);
lean_dec_ref(v_val_3040_);
lean_dec_ref(v_sym_3025_);
if (v___x_3041_ == 0)
{
goto v___jp_3032_;
}
else
{
lean_dec_ref(v_errorMsg_3026_);
return v_s_3031_;
}
}
case 3:
{
lean_object* v_rawVal_3042_; lean_object* v_info_3043_; lean_object* v_str_3044_; lean_object* v_startPos_3045_; lean_object* v_stopPos_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v_rawVal_3042_ = lean_ctor_get(v___x_3039_, 1);
lean_inc_ref(v_rawVal_3042_);
v_info_3043_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_info_3043_);
lean_dec_ref_known(v___x_3039_, 4);
v_str_3044_ = lean_ctor_get(v_rawVal_3042_, 0);
lean_inc_ref(v_str_3044_);
v_startPos_3045_ = lean_ctor_get(v_rawVal_3042_, 1);
lean_inc(v_startPos_3045_);
v_stopPos_3046_ = lean_ctor_get(v_rawVal_3042_, 2);
lean_inc(v_stopPos_3046_);
lean_dec_ref(v_rawVal_3042_);
v___x_3047_ = lean_string_utf8_extract(v_str_3044_, v_startPos_3045_, v_stopPos_3046_);
lean_dec(v_stopPos_3046_);
lean_dec(v_startPos_3045_);
lean_dec_ref(v_str_3044_);
v___x_3048_ = lean_string_dec_eq(v_sym_3025_, v___x_3047_);
lean_dec_ref(v___x_3047_);
if (v___x_3048_ == 0)
{
lean_dec(v_info_3043_);
lean_dec_ref(v_sym_3025_);
goto v___jp_3032_;
}
else
{
lean_object* v_s_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec_ref(v_errorMsg_3026_);
v_s_3049_ = l_Lean_Parser_ParserState_popSyntax(v_s_3031_);
v___x_3050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3050_, 0, v_info_3043_);
lean_ctor_set(v___x_3050_, 1, v_sym_3025_);
v___x_3051_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3049_, v___x_3050_);
return v___x_3051_;
}
}
default: 
{
lean_dec(v___x_3039_);
lean_dec_ref(v_sym_3025_);
goto v___jp_3032_;
}
}
}
v___jp_3032_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3031_, v_errorMsg_3026_, v___x_3033_);
return v___x_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3055_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3056_ = lean_string_append(v___x_3055_, v_sym_3052_);
v___x_3057_ = lean_string_append(v___x_3056_, v___x_3055_);
v___x_3058_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3052_, v___x_3057_, v_a_3053_, v_a_3054_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3063_, uint8_t v_includeIdent_3064_){
_start:
{
lean_object* v___f_3065_; lean_object* v___f_3066_; 
v___f_3065_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3066_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3064_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3068_, 0, v_sym_3063_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3070_, 0, v___f_3065_);
lean_ctor_set(v___x_3070_, 1, v___f_3066_);
lean_ctor_set(v___x_3070_, 2, v___x_3069_);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_sym_3063_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3074_, 0, v___f_3065_);
lean_ctor_set(v___x_3074_, 1, v___f_3066_);
lean_ctor_set(v___x_3074_, 2, v___x_3073_);
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3075_, lean_object* v_includeIdent_3076_){
_start:
{
uint8_t v_includeIdent_boxed_3077_; lean_object* v_res_3078_; 
v_includeIdent_boxed_3077_ = lean_unbox(v_includeIdent_3076_);
v_res_3078_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3075_, v_includeIdent_boxed_3077_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3079_, uint8_t v_includeIdent_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v_str_3085_; lean_object* v_startInclusive_3086_; lean_object* v_endExclusive_3087_; lean_object* v_sym_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_string_utf8_byte_size(v_sym_3079_);
v___x_3083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3083_, 0, v_sym_3079_);
lean_ctor_set(v___x_3083_, 1, v___x_3081_);
lean_ctor_set(v___x_3083_, 2, v___x_3082_);
v___x_3084_ = l_String_Slice_trimAscii(v___x_3083_);
v_str_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc_ref(v_str_3085_);
v_startInclusive_3086_ = lean_ctor_get(v___x_3084_, 1);
lean_inc(v_startInclusive_3086_);
v_endExclusive_3087_ = lean_ctor_get(v___x_3084_, 2);
lean_inc(v_endExclusive_3087_);
lean_dec_ref(v___x_3084_);
v_sym_3088_ = lean_string_utf8_extract_fast(v_str_3085_, v_startInclusive_3086_, v_endExclusive_3087_);
lean_dec(v_endExclusive_3087_);
lean_dec(v_startInclusive_3086_);
lean_dec_ref(v_str_3085_);
lean_inc_ref(v_sym_3088_);
v___x_3089_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3088_, v_includeIdent_3080_);
v___x_3090_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3090_, 0, v_sym_3088_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3092_, lean_object* v_includeIdent_3093_){
_start:
{
uint8_t v_includeIdent_boxed_3094_; lean_object* v_res_3095_; 
v_includeIdent_boxed_3094_ = lean_unbox(v_includeIdent_3093_);
v_res_3095_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3092_, v_includeIdent_boxed_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3096_, lean_object* v_errorMsg_3097_, lean_object* v_j_3098_, lean_object* v_c_3099_, lean_object* v_s_3100_){
_start:
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_string_utf8_at_end(v_sym_3096_, v_j_3098_);
if (v___x_3101_ == 0)
{
lean_object* v_pos_3102_; lean_object* v_toInputContext_3103_; uint8_t v___x_3104_; 
v_pos_3102_ = lean_ctor_get(v_s_3100_, 2);
v_toInputContext_3103_ = lean_ctor_get(v_c_3099_, 0);
v___x_3104_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3103_, v_pos_3102_);
if (v___x_3104_ == 0)
{
lean_object* v_inputString_3105_; uint32_t v___x_3106_; uint32_t v___x_3107_; uint8_t v___x_3108_; 
v_inputString_3105_ = lean_ctor_get(v_toInputContext_3103_, 0);
v___x_3106_ = lean_string_utf8_get_fast(v_sym_3096_, v_j_3098_);
v___x_3107_ = lean_string_utf8_get_fast(v_inputString_3105_, v_pos_3102_);
v___x_3108_ = lean_uint32_dec_eq(v___x_3106_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_dec(v_j_3098_);
v___x_3109_ = l_Lean_Parser_ParserState_mkError(v_s_3100_, v_errorMsg_3097_);
return v___x_3109_;
}
else
{
if (v___x_3104_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_inc(v_pos_3102_);
v___x_3110_ = lean_string_utf8_next_fast(v_sym_3096_, v_j_3098_);
lean_dec(v_j_3098_);
v___x_3111_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3100_, v_c_3099_, v_pos_3102_);
lean_dec(v_pos_3102_);
v_j_3098_ = v___x_3110_;
v_s_3100_ = v___x_3111_;
goto _start;
}
else
{
lean_object* v___x_3113_; 
lean_dec(v_j_3098_);
v___x_3113_ = l_Lean_Parser_ParserState_mkError(v_s_3100_, v_errorMsg_3097_);
return v___x_3113_;
}
}
}
else
{
lean_object* v___x_3114_; 
lean_dec(v_j_3098_);
v___x_3114_ = l_Lean_Parser_ParserState_mkError(v_s_3100_, v_errorMsg_3097_);
return v___x_3114_;
}
}
else
{
lean_dec(v_j_3098_);
lean_dec_ref(v_errorMsg_3097_);
return v_s_3100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3115_, lean_object* v_errorMsg_3116_, lean_object* v_j_3117_, lean_object* v_c_3118_, lean_object* v_s_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3115_, v_errorMsg_3116_, v_j_3117_, v_c_3118_, v_s_3119_);
lean_dec_ref(v_c_3118_);
lean_dec_ref(v_sym_3115_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3121_, lean_object* v_errorMsg_3122_, lean_object* v_j_3123_, lean_object* v_c_3124_, lean_object* v_s_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3121_, v_errorMsg_3122_, v_j_3123_, v_c_3124_, v_s_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3127_, lean_object* v_errorMsg_3128_, lean_object* v_j_3129_, lean_object* v_c_3130_, lean_object* v_s_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Parser_strAux(v_sym_3127_, v_errorMsg_3128_, v_j_3129_, v_c_3130_, v_s_3131_);
lean_dec_ref(v_c_3130_);
lean_dec_ref(v_sym_3127_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3133_, lean_object* v_i_3134_){
_start:
{
lean_object* v_zero_3135_; uint8_t v_isZero_3136_; 
v_zero_3135_ = lean_unsigned_to_nat(0u);
v_isZero_3136_ = lean_nat_dec_eq(v_i_3134_, v_zero_3135_);
if (v_isZero_3136_ == 1)
{
lean_object* v___x_3137_; 
lean_dec(v_i_3134_);
v___x_3137_ = lean_box(0);
return v___x_3137_;
}
else
{
lean_object* v_one_3138_; lean_object* v_n_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_one_3138_ = lean_unsigned_to_nat(1u);
v_n_3139_ = lean_nat_sub(v_i_3134_, v_one_3138_);
lean_dec(v_i_3134_);
v___x_3140_ = l_Subarray_get___redArg(v_as_3133_, v_n_3139_);
v___x_3141_ = l_Lean_Syntax_isNone(v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
lean_dec(v_n_3139_);
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
return v___x_3142_;
}
else
{
lean_dec(v___x_3140_);
v_i_3134_ = v_n_3139_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3144_, lean_object* v_i_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3144_, v_i_3145_);
lean_dec_ref(v_as_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3147_){
_start:
{
lean_object* v___x_3148_; lean_object* v_start_3149_; lean_object* v_stop_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3148_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3147_);
v_start_3149_ = lean_ctor_get(v___x_3148_, 1);
v_stop_3150_ = lean_ctor_get(v___x_3148_, 2);
v___x_3151_ = lean_nat_sub(v_stop_3150_, v_start_3149_);
v___x_3152_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3148_, v___x_3151_);
lean_dec_ref(v___x_3148_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_box(0);
return v___x_3153_;
}
else
{
lean_object* v_val_3154_; 
v_val_3154_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_val_3154_);
lean_dec_ref_known(v___x_3152_, 1);
return v_val_3154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3155_, lean_object* v_i_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3155_, v_i_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3159_, lean_object* v_i_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3159_, v_i_3160_, v_a_3161_);
lean_dec_ref(v_as_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_Syntax_getTailInfo(v_prev_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_trailing_3165_; lean_object* v_startPos_3166_; lean_object* v_stopPos_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_trailing_3165_ = lean_ctor_get(v___x_3164_, 2);
lean_inc_ref(v_trailing_3165_);
lean_dec_ref_known(v___x_3164_, 4);
v_startPos_3166_ = lean_ctor_get(v_trailing_3165_, 1);
lean_inc(v_startPos_3166_);
v_stopPos_3167_ = lean_ctor_get(v_trailing_3165_, 2);
lean_inc(v_stopPos_3167_);
lean_dec_ref(v_trailing_3165_);
v___x_3168_ = lean_unsigned_to_nat(1u);
v___x_3169_ = lean_nat_add(v_startPos_3166_, v___x_3168_);
lean_dec(v_startPos_3166_);
v___x_3170_ = lean_nat_dec_le(v___x_3169_, v_stopPos_3167_);
lean_dec(v_stopPos_3167_);
lean_dec(v___x_3169_);
return v___x_3170_;
}
else
{
uint8_t v___x_3171_; 
lean_dec(v___x_3164_);
v___x_3171_ = 0;
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3172_){
_start:
{
uint8_t v_res_3173_; lean_object* v_r_3174_; 
v_res_3173_ = l_Lean_Parser_checkTailWs(v_prev_3172_);
lean_dec(v_prev_3172_);
v_r_3174_ = lean_box(v_res_3173_);
return v_r_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3175_, lean_object* v_s_3176_){
_start:
{
lean_object* v_stxStack_3177_; lean_object* v_prev_3178_; uint8_t v___x_3179_; 
v_stxStack_3177_ = lean_ctor_get(v_s_3176_, 0);
lean_inc_ref(v_stxStack_3177_);
v_prev_3178_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3177_);
v___x_3179_ = l_Lean_Parser_checkTailWs(v_prev_3178_);
lean_dec(v_prev_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Parser_ParserState_mkError(v_s_3176_, v_errorMsg_3175_);
return v___x_3180_;
}
else
{
lean_dec_ref(v_errorMsg_3175_);
return v_s_3176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3181_, lean_object* v_x_3182_, lean_object* v_s_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3181_, v_s_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3185_, lean_object* v_x_3186_, lean_object* v_s_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3185_, v_x_3186_, v_s_3187_);
lean_dec_ref(v_x_3186_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3189_){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3191_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3191_, 0, v_errorMsg_3189_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3201_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3202_ = l_Lean_addBuiltinDocString(v___x_3200_, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = l_String_instInhabitedSlice;
v___x_3207_ = lean_panic_fn_borrowed(v___x_3206_, v_msg_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3208_, lean_object* v_a_3209_, uint8_t v_b_3210_){
_start:
{
lean_object* v_str_3211_; lean_object* v_startInclusive_3212_; lean_object* v_endExclusive_3213_; lean_object* v___x_3214_; uint8_t v_decide_3215_; 
v_str_3211_ = lean_ctor_get(v_s_3208_, 0);
v_startInclusive_3212_ = lean_ctor_get(v_s_3208_, 1);
v_endExclusive_3213_ = lean_ctor_get(v_s_3208_, 2);
v___x_3214_ = lean_nat_sub(v_endExclusive_3213_, v_startInclusive_3212_);
v_decide_3215_ = lean_nat_dec_eq(v_a_3209_, v___x_3214_);
lean_dec(v___x_3214_);
if (v_decide_3215_ == 0)
{
uint32_t v___x_3216_; lean_object* v___x_3217_; uint32_t v___x_3218_; uint8_t v___x_3219_; 
v___x_3216_ = 10;
v___x_3217_ = lean_nat_add(v_startInclusive_3212_, v_a_3209_);
lean_dec(v_a_3209_);
v___x_3218_ = lean_string_utf8_get_fast(v_str_3211_, v___x_3217_);
v___x_3219_ = lean_uint32_dec_eq(v___x_3218_, v___x_3216_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_string_utf8_next_fast(v_str_3211_, v___x_3217_);
lean_dec(v___x_3217_);
v___x_3221_ = lean_nat_sub(v___x_3220_, v_startInclusive_3212_);
v_a_3209_ = v___x_3221_;
v_b_3210_ = v___x_3219_;
goto _start;
}
else
{
lean_dec(v___x_3217_);
return v___x_3219_;
}
}
else
{
lean_dec(v_a_3209_);
return v_b_3210_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3223_, lean_object* v_a_3224_, lean_object* v_b_3225_){
_start:
{
uint8_t v_b_boxed_3226_; uint8_t v_res_3227_; lean_object* v_r_3228_; 
v_b_boxed_3226_ = lean_unbox(v_b_3225_);
v_res_3227_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3223_, v_a_3224_, v_b_boxed_3226_);
lean_dec_ref(v_s_3223_);
v_r_3228_ = lean_box(v_res_3227_);
return v_r_3228_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3229_){
_start:
{
lean_object* v_searcher_3230_; uint8_t v___x_3231_; uint8_t v___x_3232_; 
v_searcher_3230_ = lean_unsigned_to_nat(0u);
v___x_3231_ = 0;
v___x_3232_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3229_, v_searcher_3230_, v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3233_){
_start:
{
uint8_t v_res_3234_; lean_object* v_r_3235_; 
v_res_3234_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3233_);
lean_dec_ref(v_s_3233_);
v_r_3235_ = lean_box(v_res_3234_);
return v_r_3235_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3239_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3240_ = lean_unsigned_to_nat(14u);
v___x_3241_ = lean_unsigned_to_nat(22u);
v___x_3242_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3243_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3244_ = l_mkPanicMessageWithDecl(v___x_3243_, v___x_3242_, v___x_3241_, v___x_3240_, v___x_3239_);
return v___x_3244_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Syntax_getTailInfo(v_prev_3245_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_trailing_3247_; lean_object* v_str_3248_; lean_object* v_startPos_3249_; lean_object* v_stopPos_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3266_; 
v_trailing_3247_ = lean_ctor_get(v___x_3246_, 2);
lean_inc_ref(v_trailing_3247_);
lean_dec_ref_known(v___x_3246_, 4);
v_str_3248_ = lean_ctor_get(v_trailing_3247_, 0);
v_startPos_3249_ = lean_ctor_get(v_trailing_3247_, 1);
v_stopPos_3250_ = lean_ctor_get(v_trailing_3247_, 2);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_trailing_3247_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3252_ = v_trailing_3247_;
v_isShared_3253_ = v_isSharedCheck_3266_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_stopPos_3250_);
lean_inc(v_startPos_3249_);
lean_inc(v_str_3248_);
lean_dec(v_trailing_3247_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3266_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint8_t v___y_3255_; uint8_t v___x_3263_; 
v___x_3263_ = lean_string_is_valid_pos(v_str_3248_, v_startPos_3249_);
if (v___x_3263_ == 0)
{
v___y_3255_ = v___x_3263_;
goto v___jp_3254_;
}
else
{
uint8_t v___x_3264_; 
v___x_3264_ = lean_string_is_valid_pos(v_str_3248_, v_stopPos_3250_);
if (v___x_3264_ == 0)
{
v___y_3255_ = v___x_3264_;
goto v___jp_3254_;
}
else
{
uint8_t v___x_3265_; 
v___x_3265_ = lean_nat_dec_le(v_startPos_3249_, v_stopPos_3250_);
v___y_3255_ = v___x_3265_;
goto v___jp_3254_;
}
}
v___jp_3254_:
{
if (v___y_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
lean_del_object(v___x_3252_);
lean_dec(v_stopPos_3250_);
lean_dec(v_startPos_3249_);
lean_dec_ref(v_str_3248_);
v___x_3256_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3257_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3256_);
v___x_3258_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3257_);
lean_dec_ref(v___x_3257_);
return v___x_3258_;
}
else
{
lean_object* v___x_3260_; 
if (v_isShared_3253_ == 0)
{
v___x_3260_ = v___x_3252_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_str_3248_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_startPos_3249_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_stopPos_3250_);
v___x_3260_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3260_);
lean_dec_ref(v___x_3260_);
return v___x_3261_;
}
}
}
}
}
else
{
uint8_t v___x_3267_; 
lean_dec(v___x_3246_);
v___x_3267_ = 0;
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_Lean_Parser_checkTailLinebreak(v_prev_3268_);
lean_dec(v_prev_3268_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3271_, lean_object* v_inst_3272_, lean_object* v_R_3273_, lean_object* v_a_3274_, uint8_t v_b_3275_, lean_object* v_c_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3271_, v_a_3274_, v_b_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3278_, lean_object* v_inst_3279_, lean_object* v_R_3280_, lean_object* v_a_3281_, lean_object* v_b_3282_, lean_object* v_c_3283_){
_start:
{
uint8_t v_b_boxed_3284_; uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_b_boxed_3284_ = lean_unbox(v_b_3282_);
v_res_3285_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3278_, v_inst_3279_, v_R_3280_, v_a_3281_, v_b_boxed_3284_, v_c_3283_);
lean_dec_ref(v_s_3278_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3287_, lean_object* v_s_3288_){
_start:
{
lean_object* v_stxStack_3289_; lean_object* v_prev_3290_; uint8_t v___x_3291_; 
v_stxStack_3289_ = lean_ctor_get(v_s_3288_, 0);
v_prev_3290_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3289_);
v___x_3291_ = l_Lean_Parser_checkTailLinebreak(v_prev_3290_);
lean_dec(v_prev_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_Parser_ParserState_mkError(v_s_3288_, v_errorMsg_3287_);
return v___x_3292_;
}
else
{
lean_dec_ref(v_errorMsg_3287_);
return v_s_3288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3293_, lean_object* v_x_3294_, lean_object* v_s_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3293_, v_s_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3297_, lean_object* v_x_3298_, lean_object* v_s_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3297_, v_x_3298_, v_s_3299_);
lean_dec_ref(v_x_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3301_){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3303_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3303_, 0, v_errorMsg_3301_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3313_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3314_ = l_Lean_addBuiltinDocString(v___x_3312_, v___x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3316_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Syntax_getTailInfo(v_prev_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_trailing_3319_; lean_object* v_startPos_3320_; lean_object* v_stopPos_3321_; uint8_t v_decide_3322_; 
v_trailing_3319_ = lean_ctor_get(v___x_3318_, 2);
lean_inc_ref(v_trailing_3319_);
lean_dec_ref_known(v___x_3318_, 4);
v_startPos_3320_ = lean_ctor_get(v_trailing_3319_, 1);
lean_inc(v_startPos_3320_);
v_stopPos_3321_ = lean_ctor_get(v_trailing_3319_, 2);
lean_inc(v_stopPos_3321_);
lean_dec_ref(v_trailing_3319_);
v_decide_3322_ = lean_nat_dec_eq(v_stopPos_3321_, v_startPos_3320_);
lean_dec(v_startPos_3320_);
lean_dec(v_stopPos_3321_);
return v_decide_3322_;
}
else
{
uint8_t v___x_3323_; 
lean_dec(v___x_3318_);
v___x_3323_ = 0;
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3324_){
_start:
{
uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_res_3325_ = l_Lean_Parser_checkTailNoWs(v_prev_3324_);
lean_dec(v_prev_3324_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3327_, lean_object* v_s_3328_){
_start:
{
lean_object* v_stxStack_3329_; lean_object* v_prev_3330_; uint8_t v___x_3331_; 
v_stxStack_3329_ = lean_ctor_get(v_s_3328_, 0);
lean_inc_ref(v_stxStack_3329_);
v_prev_3330_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3329_);
v___x_3331_ = l_Lean_Parser_checkTailNoWs(v_prev_3330_);
lean_dec(v_prev_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Parser_ParserState_mkError(v_s_3328_, v_errorMsg_3327_);
return v___x_3332_;
}
else
{
lean_dec_ref(v_errorMsg_3327_);
return v_s_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3333_, lean_object* v_x_3334_, lean_object* v_s_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3333_, v_s_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3337_, lean_object* v_x_3338_, lean_object* v_s_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3337_, v_x_3338_, v_s_3339_);
lean_dec_ref(v_x_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3341_){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3343_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3343_, 0, v_errorMsg_3341_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3353_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3354_ = l_Lean_addBuiltinDocString(v___x_3352_, v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3356_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3357_, lean_object* v_asciiSym_3358_, lean_object* v_s_3359_){
_start:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_string_dec_eq(v_s_3359_, v_sym_3357_);
if (v___x_3360_ == 0)
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_string_dec_eq(v_s_3359_, v_asciiSym_3358_);
return v___x_3361_;
}
else
{
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3362_, lean_object* v_asciiSym_3363_, lean_object* v_s_3364_){
_start:
{
uint8_t v_res_3365_; lean_object* v_r_3366_; 
v_res_3365_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3362_, v_asciiSym_3363_, v_s_3364_);
lean_dec_ref(v_s_3364_);
lean_dec_ref(v_asciiSym_3363_);
lean_dec_ref(v_sym_3362_);
v_r_3366_ = lean_box(v_res_3365_);
return v_r_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3367_, lean_object* v_asciiSym_3368_, lean_object* v_expected_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___f_3372_; lean_object* v___x_3373_; 
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3372_, 0, v_sym_3367_);
lean_closure_set(v___f_3372_, 1, v_asciiSym_3368_);
v___x_3373_ = l_Lean_Parser_satisfySymbolFn(v___f_3372_, v_expected_3369_, v_a_3370_, v_a_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3374_, lean_object* v_sym_3375_, lean_object* v_tks_3376_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3377_, 0, v_asciiSym_3374_);
lean_ctor_set(v___x_3377_, 1, v_tks_3376_);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_sym_3375_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3379_, lean_object* v_asciiSym_3380_){
_start:
{
lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_inc_ref(v_sym_3379_);
lean_inc_ref(v_asciiSym_3380_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3381_, 0, v_asciiSym_3380_);
lean_closure_set(v___f_3381_, 1, v_sym_3379_);
v___f_3382_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3383_ = lean_box(0);
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v_asciiSym_3380_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_sym_3379_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3387_, 0, v___f_3381_);
lean_ctor_set(v___x_3387_, 1, v___f_3382_);
lean_ctor_set(v___x_3387_, 2, v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3389_, lean_object* v_asciiSym_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3393_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3394_ = lean_string_append(v___x_3393_, v_sym_3389_);
v___x_3395_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
v___x_3397_ = lean_string_append(v___x_3396_, v_asciiSym_3390_);
v___x_3398_ = lean_string_append(v___x_3397_, v___x_3393_);
v___x_3399_ = lean_box(0);
v___x_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3389_, v_asciiSym_3390_, v___x_3400_, v_a_3391_, v_a_3392_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3402_, lean_object* v_asciiSym_3403_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_str_3408_; lean_object* v_startInclusive_3409_; lean_object* v_endExclusive_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3427_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_string_utf8_byte_size(v_sym_3402_);
v___x_3406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3406_, 0, v_sym_3402_);
lean_ctor_set(v___x_3406_, 1, v___x_3404_);
lean_ctor_set(v___x_3406_, 2, v___x_3405_);
v___x_3407_ = l_String_Slice_trimAscii(v___x_3406_);
v_str_3408_ = lean_ctor_get(v___x_3407_, 0);
v_startInclusive_3409_ = lean_ctor_get(v___x_3407_, 1);
v_endExclusive_3410_ = lean_ctor_get(v___x_3407_, 2);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3412_ = v___x_3407_;
v_isShared_3413_ = v_isSharedCheck_3427_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_endExclusive_3410_);
lean_inc(v_startInclusive_3409_);
lean_inc(v_str_3408_);
lean_dec(v___x_3407_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3427_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = lean_string_utf8_byte_size(v_asciiSym_3403_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 2, v___x_3414_);
lean_ctor_set(v___x_3412_, 1, v___x_3404_);
lean_ctor_set(v___x_3412_, 0, v_asciiSym_3403_);
v___x_3416_ = v___x_3412_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_asciiSym_3403_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v_str_3418_; lean_object* v_startInclusive_3419_; lean_object* v_endExclusive_3420_; lean_object* v_sym_3421_; lean_object* v_asciiSym_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3417_ = l_String_Slice_trimAscii(v___x_3416_);
v_str_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc_ref(v_str_3418_);
v_startInclusive_3419_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_startInclusive_3419_);
v_endExclusive_3420_ = lean_ctor_get(v___x_3417_, 2);
lean_inc(v_endExclusive_3420_);
lean_dec_ref(v___x_3417_);
v_sym_3421_ = lean_string_utf8_extract_fast(v_str_3408_, v_startInclusive_3409_, v_endExclusive_3410_);
lean_dec(v_endExclusive_3410_);
lean_dec(v_startInclusive_3409_);
lean_dec_ref(v_str_3408_);
v_asciiSym_3422_ = lean_string_utf8_extract_fast(v_str_3418_, v_startInclusive_3419_, v_endExclusive_3420_);
lean_dec(v_endExclusive_3420_);
lean_dec(v_startInclusive_3419_);
lean_dec_ref(v_str_3418_);
lean_inc_ref(v_asciiSym_3422_);
lean_inc_ref(v_sym_3421_);
v___x_3423_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3421_, v_asciiSym_3422_);
v___x_3424_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3424_, 0, v_sym_3421_);
lean_closure_set(v___x_3424_, 1, v_asciiSym_3422_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3428_, lean_object* v_asciiSym_3429_, uint8_t v_preserveForPP_3430_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3428_, v_asciiSym_3429_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3432_, lean_object* v_asciiSym_3433_, lean_object* v_preserveForPP_3434_){
_start:
{
uint8_t v_preserveForPP_boxed_3435_; lean_object* v_res_3436_; 
v_preserveForPP_boxed_3435_ = lean_unbox(v_preserveForPP_3434_);
v_res_3436_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3432_, v_asciiSym_3433_, v_preserveForPP_boxed_3435_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3437_){
_start:
{
lean_object* v___f_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___f_3438_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3439_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3441_, 0, v_k_3437_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
v___x_3443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3443_, 0, v___f_3438_);
lean_ctor_set(v___x_3443_, 1, v___f_3439_);
lean_ctor_set(v___x_3443_, 2, v___x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3444_, lean_object* v_desc_3445_, lean_object* v_c_3446_, lean_object* v_s_3447_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v_s_3450_; lean_object* v_stxStack_3451_; lean_object* v_errorMsg_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3448_ = lean_box(0);
lean_inc_ref(v_desc_3445_);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_desc_3445_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v_s_3450_ = l_Lean_Parser_tokenFn(v___x_3449_, v_c_3446_, v_s_3447_);
v_stxStack_3451_ = lean_ctor_get(v_s_3450_, 0);
v_errorMsg_3452_ = lean_ctor_get(v_s_3450_, 4);
v___x_3453_ = lean_box(0);
v___x_3454_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3452_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_dec_ref(v_desc_3445_);
return v_s_3450_;
}
else
{
lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3455_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3451_);
v___x_3456_ = l_Lean_Syntax_isOfKind(v___x_3455_, v_k_3444_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_unsigned_to_nat(0u);
v___x_3458_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3450_, v_desc_3445_, v___x_3457_);
return v___x_3458_;
}
else
{
lean_dec_ref(v_desc_3445_);
return v_s_3450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3459_, lean_object* v_desc_3460_, lean_object* v_c_3461_, lean_object* v_s_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Parser_expectTokenFn(v_k_3459_, v_desc_3460_, v_c_3461_, v_s_3462_);
lean_dec(v_k_3459_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3467_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3468_ = l_Lean_Parser_expectTokenFn(v___x_3466_, v___x_3467_, v_a_3464_, v_a_3465_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3470_ = l_Lean_Parser_mkAtomicInfo(v___x_3469_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3472_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v___x_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3478_, lean_object* v_s_3479_){
_start:
{
lean_object* v_pos_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_pos_3480_ = lean_ctor_get(v_s_3479_, 2);
lean_inc(v_pos_3480_);
v___x_3481_ = 1;
v___x_3482_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3483_ = l_Lean_Parser_hexNumberFn(v_pos_3480_, v___x_3481_, v___x_3482_, v_ctx_3478_, v_s_3479_);
return v___x_3483_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3485_ = l_Lean_Parser_mkAtomicInfo(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3487_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3494_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3495_ = l_Lean_Parser_expectTokenFn(v___x_3493_, v___x_3494_, v_a_3491_, v_a_3492_);
return v___x_3495_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3497_ = l_Lean_Parser_mkAtomicInfo(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3499_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3506_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3507_ = l_Lean_Parser_expectTokenFn(v___x_3505_, v___x_3506_, v_a_3503_, v_a_3504_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3509_ = l_Lean_Parser_mkAtomicInfo(v___x_3508_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3511_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v___x_3510_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3518_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3519_ = l_Lean_Parser_expectTokenFn(v___x_3517_, v___x_3518_, v_a_3515_, v_a_3516_);
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3521_ = l_Lean_Parser_mkAtomicInfo(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3523_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v___x_3522_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3533_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3534_ = l_Lean_Parser_expectTokenFn(v___x_3532_, v___x_3533_, v_a_3530_, v_a_3531_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3536_ = l_Lean_Parser_mkAtomicInfo(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3538_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_c_3544_, lean_object* v_s_3545_){
_start:
{
lean_object* v_toCacheableParserContext_3546_; lean_object* v_forbiddenTks_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v_toCacheableParserContext_3546_ = lean_ctor_get(v_c_3544_, 2);
v_forbiddenTks_3547_ = lean_ctor_get(v_toCacheableParserContext_3546_, 3);
v___x_3548_ = lean_array_get_size(v_forbiddenTks_3547_);
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = lean_nat_dec_eq(v___x_3548_, v___x_3549_);
if (v___x_3550_ == 0)
{
lean_object* v_pos_3551_; lean_object* v_iniSz_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v_s_3555_; lean_object* v_stxStack_3556_; lean_object* v_errorMsg_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
lean_inc_ref(v_forbiddenTks_3547_);
v_pos_3551_ = lean_ctor_get(v_s_3545_, 2);
lean_inc(v_pos_3551_);
v_iniSz_3552_ = l_Lean_Parser_ParserState_stackSize(v_s_3545_);
v___x_3553_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3554_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v_s_3555_ = l_Lean_Parser_expectTokenFn(v___x_3553_, v___x_3554_, v_c_3544_, v_s_3545_);
v_stxStack_3556_ = lean_ctor_get(v_s_3555_, 0);
v_errorMsg_3557_ = lean_ctor_get(v_s_3555_, 4);
v___x_3558_ = lean_box(0);
v___x_3559_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3557_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_dec(v_iniSz_3552_);
lean_dec(v_pos_3551_);
lean_dec_ref(v_forbiddenTks_3547_);
return v_s_3555_;
}
else
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3556_);
if (lean_obj_tag(v___x_3560_) == 3)
{
lean_object* v_rawVal_3561_; lean_object* v_str_3562_; lean_object* v_startPos_3563_; lean_object* v_stopPos_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v_rawVal_3561_ = lean_ctor_get(v___x_3560_, 1);
lean_inc_ref(v_rawVal_3561_);
lean_dec_ref_known(v___x_3560_, 4);
v_str_3562_ = lean_ctor_get(v_rawVal_3561_, 0);
lean_inc_ref(v_str_3562_);
v_startPos_3563_ = lean_ctor_get(v_rawVal_3561_, 1);
lean_inc(v_startPos_3563_);
v_stopPos_3564_ = lean_ctor_get(v_rawVal_3561_, 2);
lean_inc(v_stopPos_3564_);
lean_dec_ref(v_rawVal_3561_);
v___x_3565_ = lean_string_utf8_extract(v_str_3562_, v_startPos_3563_, v_stopPos_3564_);
lean_dec(v_stopPos_3564_);
lean_dec(v_startPos_3563_);
lean_dec_ref(v_str_3562_);
v___x_3566_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_3547_, v___x_3565_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v_forbiddenTks_3547_);
if (v___x_3566_ == 0)
{
lean_dec(v_iniSz_3552_);
lean_dec(v_pos_3551_);
return v_s_3555_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_iniSz_3552_);
v___x_3569_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_3555_, v___x_3567_, v_pos_3551_, v___x_3568_);
lean_dec_ref_known(v___x_3568_, 1);
return v___x_3569_;
}
}
else
{
lean_dec(v___x_3560_);
lean_dec(v_iniSz_3552_);
lean_dec(v_pos_3551_);
lean_dec_ref(v_forbiddenTks_3547_);
return v_s_3555_;
}
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3571_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3572_ = l_Lean_Parser_expectTokenFn(v___x_3570_, v___x_3571_, v_c_3544_, v_s_3545_);
return v___x_3572_;
}
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3574_ = l_Lean_Parser_mkAtomicInfo(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3576_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v___x_3575_);
return v___x_3577_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3590_, lean_object* v_c_3591_, lean_object* v_s_3592_){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v_s_3595_; lean_object* v_stxStack_3596_; lean_object* v_errorMsg_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3593_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3594_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3595_ = l_Lean_Parser_tokenFn(v___x_3594_, v_c_3591_, v_s_3592_);
v_stxStack_3596_ = lean_ctor_get(v_s_3595_, 0);
v_errorMsg_3597_ = lean_ctor_get(v_s_3595_, 4);
v___x_3598_ = lean_box(0);
v___x_3599_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_dec(v_id_3590_);
return v_s_3595_;
}
else
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3596_);
if (lean_obj_tag(v___x_3600_) == 3)
{
lean_object* v_val_3601_; uint8_t v___x_3602_; 
v_val_3601_ = lean_ctor_get(v___x_3600_, 2);
lean_inc(v_val_3601_);
lean_dec_ref_known(v___x_3600_, 4);
v___x_3602_ = lean_name_eq(v_val_3601_, v_id_3590_);
lean_dec(v_val_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3603_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3604_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3590_, v___x_3599_);
v___x_3605_ = lean_string_append(v___x_3603_, v___x_3604_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3607_ = lean_string_append(v___x_3605_, v___x_3606_);
v___x_3608_ = lean_unsigned_to_nat(0u);
v___x_3609_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3595_, v___x_3607_, v___x_3608_);
return v___x_3609_;
}
else
{
lean_dec(v_id_3590_);
return v_s_3595_;
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_dec(v___x_3600_);
lean_dec(v_id_3590_);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3595_, v___x_3593_, v___x_3610_);
return v___x_3611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3612_){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3614_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3614_, 0, v_id_3612_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3619_, lean_object* v_s_3620_){
_start:
{
lean_object* v_pos_3622_; lean_object* v_str_3623_; lean_object* v_trailing_3624_; lean_object* v_s_3625_; lean_object* v_stxStack_3637_; lean_object* v_pos_3638_; uint8_t v___x_3641_; 
v_stxStack_3637_ = lean_ctor_get(v_s_3620_, 0);
v_pos_3638_ = lean_ctor_get(v_s_3620_, 2);
v___x_3641_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3637_);
if (v___x_3641_ == 0)
{
lean_object* v_prev_3642_; lean_object* v___x_3643_; 
v_prev_3642_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3637_);
v___x_3643_ = l_Lean_Syntax_getTailInfo(v_prev_3642_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_leading_3644_; lean_object* v_pos_3645_; lean_object* v_trailing_3646_; lean_object* v_endPos_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3658_; 
v_leading_3644_ = lean_ctor_get(v___x_3643_, 0);
v_pos_3645_ = lean_ctor_get(v___x_3643_, 1);
v_trailing_3646_ = lean_ctor_get(v___x_3643_, 2);
v_endPos_3647_ = lean_ctor_get(v___x_3643_, 3);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3649_ = v___x_3643_;
v_isShared_3650_ = v_isSharedCheck_3658_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_endPos_3647_);
lean_inc(v_trailing_3646_);
lean_inc(v_pos_3645_);
lean_inc(v_leading_3644_);
lean_dec(v___x_3643_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3658_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_str_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
lean_inc_n(v_endPos_3647_, 2);
v_str_3651_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3619_, v_endPos_3647_);
v___x_3652_ = l_Lean_Parser_ParserState_popSyntax(v_s_3620_);
lean_inc_ref(v_str_3651_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 2, v_str_3651_);
v___x_3654_ = v___x_3649_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_leading_3644_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_pos_3645_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_str_3651_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_endPos_3647_);
v___x_3654_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v_s_3656_; 
v___x_3655_ = l_Lean_Syntax_setTailInfo(v_prev_3642_, v___x_3654_);
v_s_3656_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3652_, v___x_3655_);
v_pos_3622_ = v_endPos_3647_;
v_str_3623_ = v_str_3651_;
v_trailing_3624_ = v_trailing_3646_;
v_s_3625_ = v_s_3656_;
goto v___jp_3621_;
}
}
}
else
{
lean_inc(v_pos_3638_);
lean_dec(v___x_3643_);
lean_dec(v_prev_3642_);
goto v___jp_3639_;
}
}
else
{
lean_inc(v_pos_3638_);
goto v___jp_3639_;
}
v___jp_3621_:
{
lean_object* v_info_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v_ident_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_inc(v_pos_3622_);
lean_inc_ref(v_str_3623_);
v_info_3626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3626_, 0, v_str_3623_);
lean_ctor_set(v_info_3626_, 1, v_pos_3622_);
lean_ctor_set(v_info_3626_, 2, v_trailing_3624_);
lean_ctor_set(v_info_3626_, 3, v_pos_3622_);
v___x_3627_ = lean_box(0);
v___x_3628_ = lean_box(0);
v_ident_3629_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3629_, 0, v_info_3626_);
lean_ctor_set(v_ident_3629_, 1, v_str_3623_);
lean_ctor_set(v_ident_3629_, 2, v___x_3627_);
lean_ctor_set(v_ident_3629_, 3, v___x_3628_);
v___x_3630_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3631_ = lean_unsigned_to_nat(1u);
v___x_3632_ = lean_mk_empty_array_with_capacity(v___x_3631_);
v___x_3633_ = lean_array_push(v___x_3632_, v_ident_3629_);
v___x_3634_ = lean_box(2);
v___x_3635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___x_3630_);
lean_ctor_set(v___x_3635_, 2, v___x_3633_);
v___x_3636_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3625_, v___x_3635_);
return v___x_3636_;
}
v___jp_3639_:
{
lean_object* v_str_3640_; 
lean_inc(v_pos_3638_);
v_str_3640_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3619_, v_pos_3638_);
lean_inc_ref(v_str_3640_);
v_pos_3622_ = v_pos_3638_;
v_str_3623_ = v_str_3640_;
v_trailing_3624_ = v_str_3640_;
v_s_3625_ = v_s_3620_;
goto v___jp_3621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3659_, lean_object* v_s_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Parser_hygieneInfoFn(v_c_3659_, v_s_3660_);
lean_dec_ref(v_c_3659_);
return v_res_3661_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3663_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3664_ = l_Lean_Parser_nodeInfo(v___x_3663_, v___x_3662_);
return v___x_3664_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3666_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v___x_3665_);
return v___x_3667_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3669_, lean_object* v_startStackSize_3670_){
_start:
{
lean_object* v_node_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v_node_3671_ = l_Lean_Parser_SyntaxStack_back(v_s_3669_);
v___x_3672_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3669_, v_startStackSize_3670_);
v___x_3673_ = l_Lean_Parser_SyntaxStack_push(v___x_3672_, v_node_3671_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3674_, lean_object* v_startStackSize_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Parser_ParserState_keepTop(v_s_3674_, v_startStackSize_3675_);
lean_dec(v_startStackSize_3675_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3677_, lean_object* v_oldStackSize_3678_){
_start:
{
lean_object* v_stxStack_3679_; lean_object* v_lhsPrec_3680_; lean_object* v_pos_3681_; lean_object* v_cache_3682_; lean_object* v_errorMsg_3683_; lean_object* v_recoveredErrors_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3692_; 
v_stxStack_3679_ = lean_ctor_get(v_s_3677_, 0);
v_lhsPrec_3680_ = lean_ctor_get(v_s_3677_, 1);
v_pos_3681_ = lean_ctor_get(v_s_3677_, 2);
v_cache_3682_ = lean_ctor_get(v_s_3677_, 3);
v_errorMsg_3683_ = lean_ctor_get(v_s_3677_, 4);
v_recoveredErrors_3684_ = lean_ctor_get(v_s_3677_, 5);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_s_3677_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3686_ = v_s_3677_;
v_isShared_3687_ = v_isSharedCheck_3692_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_recoveredErrors_3684_);
lean_inc(v_errorMsg_3683_);
lean_inc(v_cache_3682_);
lean_inc(v_pos_3681_);
lean_inc(v_lhsPrec_3680_);
lean_inc(v_stxStack_3679_);
lean_dec(v_s_3677_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3692_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3679_, v_oldStackSize_3678_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3688_);
v___x_3690_ = v___x_3686_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_lhsPrec_3680_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_pos_3681_);
lean_ctor_set(v_reuseFailAlloc_3691_, 3, v_cache_3682_);
lean_ctor_set(v_reuseFailAlloc_3691_, 4, v_errorMsg_3683_);
lean_ctor_set(v_reuseFailAlloc_3691_, 5, v_recoveredErrors_3684_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3693_, lean_object* v_oldStackSize_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_Parser_ParserState_keepNewError(v_s_3693_, v_oldStackSize_3694_);
lean_dec(v_oldStackSize_3694_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3696_, lean_object* v_oldStackSize_3697_, lean_object* v_oldStopPos_3698_, lean_object* v_oldError_3699_, lean_object* v_oldLhsPrec_3700_){
_start:
{
lean_object* v_stxStack_3701_; lean_object* v_cache_3702_; lean_object* v_recoveredErrors_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3711_; 
v_stxStack_3701_ = lean_ctor_get(v_s_3696_, 0);
v_cache_3702_ = lean_ctor_get(v_s_3696_, 3);
v_recoveredErrors_3703_ = lean_ctor_get(v_s_3696_, 5);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_s_3696_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; lean_object* v_unused_3713_; lean_object* v_unused_3714_; 
v_unused_3712_ = lean_ctor_get(v_s_3696_, 4);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_s_3696_, 2);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_s_3696_, 1);
lean_dec(v_unused_3714_);
v___x_3705_ = v_s_3696_;
v_isShared_3706_ = v_isSharedCheck_3711_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_recoveredErrors_3703_);
lean_inc(v_cache_3702_);
lean_inc(v_stxStack_3701_);
lean_dec(v_s_3696_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3711_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3701_, v_oldStackSize_3697_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 4, v_oldError_3699_);
lean_ctor_set(v___x_3705_, 2, v_oldStopPos_3698_);
lean_ctor_set(v___x_3705_, 1, v_oldLhsPrec_3700_);
lean_ctor_set(v___x_3705_, 0, v___x_3707_);
v___x_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_oldLhsPrec_3700_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_oldStopPos_3698_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_cache_3702_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_oldError_3699_);
lean_ctor_set(v_reuseFailAlloc_3710_, 5, v_recoveredErrors_3703_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3715_, lean_object* v_oldStackSize_3716_, lean_object* v_oldStopPos_3717_, lean_object* v_oldError_3718_, lean_object* v_oldLhsPrec_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3715_, v_oldStackSize_3716_, v_oldStopPos_3717_, v_oldError_3718_, v_oldLhsPrec_3719_);
lean_dec(v_oldStackSize_3716_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3721_, lean_object* v_oldStackSize_3722_, lean_object* v_oldError_3723_){
_start:
{
lean_object* v_stxStack_3724_; lean_object* v_lhsPrec_3725_; lean_object* v_pos_3726_; lean_object* v_cache_3727_; lean_object* v_errorMsg_3728_; lean_object* v_recoveredErrors_3729_; lean_object* v___y_3731_; 
v_stxStack_3724_ = lean_ctor_get(v_s_3721_, 0);
v_lhsPrec_3725_ = lean_ctor_get(v_s_3721_, 1);
v_pos_3726_ = lean_ctor_get(v_s_3721_, 2);
v_cache_3727_ = lean_ctor_get(v_s_3721_, 3);
v_errorMsg_3728_ = lean_ctor_get(v_s_3721_, 4);
v_recoveredErrors_3729_ = lean_ctor_get(v_s_3721_, 5);
if (lean_obj_tag(v_errorMsg_3728_) == 1)
{
lean_object* v_val_3735_; uint8_t v___x_3736_; 
lean_inc_ref(v_errorMsg_3728_);
lean_inc_ref(v_recoveredErrors_3729_);
lean_inc_ref(v_cache_3727_);
lean_inc(v_pos_3726_);
lean_inc(v_lhsPrec_3725_);
lean_inc_ref(v_stxStack_3724_);
lean_dec_ref(v_s_3721_);
v_val_3735_ = lean_ctor_get(v_errorMsg_3728_, 0);
lean_inc(v_val_3735_);
lean_dec_ref_known(v_errorMsg_3728_, 1);
v___x_3736_ = l_Lean_Parser_instBEqError_beq(v_oldError_3723_, v_val_3735_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Parser_Error_merge(v_oldError_3723_, v_val_3735_);
v___y_3731_ = v___x_3737_;
goto v___jp_3730_;
}
else
{
lean_dec_ref(v_oldError_3723_);
v___y_3731_ = v_val_3735_;
goto v___jp_3730_;
}
}
else
{
lean_dec_ref(v_oldError_3723_);
return v_s_3721_;
}
v___jp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3724_, v_oldStackSize_3722_);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___y_3731_);
v___x_3734_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v_lhsPrec_3725_);
lean_ctor_set(v___x_3734_, 2, v_pos_3726_);
lean_ctor_set(v___x_3734_, 3, v_cache_3727_);
lean_ctor_set(v___x_3734_, 4, v___x_3733_);
lean_ctor_set(v___x_3734_, 5, v_recoveredErrors_3729_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3738_, lean_object* v_oldStackSize_3739_, lean_object* v_oldError_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3738_, v_oldStackSize_3739_, v_oldError_3740_);
lean_dec(v_oldStackSize_3739_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3742_, lean_object* v_startStackSize_3743_){
_start:
{
lean_object* v_stxStack_3744_; lean_object* v_lhsPrec_3745_; lean_object* v_pos_3746_; lean_object* v_cache_3747_; lean_object* v_recoveredErrors_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3757_; 
v_stxStack_3744_ = lean_ctor_get(v_s_3742_, 0);
v_lhsPrec_3745_ = lean_ctor_get(v_s_3742_, 1);
v_pos_3746_ = lean_ctor_get(v_s_3742_, 2);
v_cache_3747_ = lean_ctor_get(v_s_3742_, 3);
v_recoveredErrors_3748_ = lean_ctor_get(v_s_3742_, 5);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_s_3742_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v_s_3742_, 4);
lean_dec(v_unused_3758_);
v___x_3750_ = v_s_3742_;
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_recoveredErrors_3748_);
lean_inc(v_cache_3747_);
lean_inc(v_pos_3746_);
lean_inc(v_lhsPrec_3745_);
lean_inc(v_stxStack_3744_);
lean_dec(v_s_3742_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3752_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3744_, v_startStackSize_3743_);
v___x_3753_ = lean_box(0);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 4, v___x_3753_);
lean_ctor_set(v___x_3750_, 0, v___x_3752_);
v___x_3755_ = v___x_3750_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_lhsPrec_3745_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_pos_3746_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_cache_3747_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3756_, 5, v_recoveredErrors_3748_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3759_, lean_object* v_startStackSize_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Parser_ParserState_keepLatest(v_s_3759_, v_startStackSize_3760_);
lean_dec(v_startStackSize_3760_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3762_, lean_object* v_startStackSize_3763_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Parser_ParserState_keepLatest(v_s_3762_, v_startStackSize_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3765_, lean_object* v_startStackSize_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3765_, v_startStackSize_3766_);
lean_dec(v_startStackSize_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3769_){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3771_ = l_Lean_Parser_ParserState_mkError(v_s_3769_, v___x_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3772_, lean_object* v_startLhsPrec_3773_, lean_object* v_p_3774_, lean_object* v_c_3775_, lean_object* v_s_3776_){
_start:
{
lean_object* v___y_3778_; lean_object* v_s_3779_; lean_object* v_stxStack_3792_; lean_object* v_pos_3793_; lean_object* v_cache_3794_; lean_object* v_errorMsg_3795_; lean_object* v_recoveredErrors_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3809_; 
v_stxStack_3792_ = lean_ctor_get(v_s_3776_, 0);
v_pos_3793_ = lean_ctor_get(v_s_3776_, 2);
v_cache_3794_ = lean_ctor_get(v_s_3776_, 3);
v_errorMsg_3795_ = lean_ctor_get(v_s_3776_, 4);
v_recoveredErrors_3796_ = lean_ctor_get(v_s_3776_, 5);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_s_3776_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v_s_3776_, 1);
lean_dec(v_unused_3810_);
v___x_3798_ = v_s_3776_;
v_isShared_3799_ = v_isSharedCheck_3809_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_recoveredErrors_3796_);
lean_inc(v_errorMsg_3795_);
lean_inc(v_cache_3794_);
lean_inc(v_pos_3793_);
lean_inc(v_stxStack_3792_);
lean_dec(v_s_3776_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3809_;
goto v_resetjp_3797_;
}
v___jp_3777_:
{
lean_object* v_s_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v_s_3780_ = lean_apply_2(v_p_3774_, v_c_3775_, v_s_3779_);
v___x_3781_ = l_Lean_Parser_ParserState_stackSize(v_s_3780_);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_add(v___y_3778_, v___x_3782_);
v___x_3784_ = lean_nat_dec_eq(v___x_3781_, v___x_3783_);
lean_dec(v___x_3783_);
lean_dec(v___x_3781_);
if (v___x_3784_ == 0)
{
lean_object* v_errorMsg_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_errorMsg_3785_ = lean_ctor_get(v_s_3780_, 4);
lean_inc(v_errorMsg_3785_);
v___x_3786_ = lean_box(0);
v___x_3787_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3785_, v___x_3786_);
lean_dec(v_errorMsg_3785_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3780_, v___y_3778_);
lean_dec(v___y_3778_);
v___x_3789_ = lean_box(0);
v___x_3790_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3788_, v___x_3789_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; 
lean_dec(v___y_3778_);
v___x_3791_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3780_);
return v___x_3791_;
}
}
else
{
lean_dec(v___y_3778_);
return v_s_3780_;
}
}
v_resetjp_3797_:
{
lean_object* v___y_3801_; 
if (lean_obj_tag(v_left_x3f_3772_) == 0)
{
lean_object* v___x_3808_; 
lean_dec(v_startLhsPrec_3773_);
v___x_3808_ = l_Lean_Parser_maxPrec;
v___y_3801_ = v___x_3808_;
goto v___jp_3800_;
}
else
{
v___y_3801_ = v_startLhsPrec_3773_;
goto v___jp_3800_;
}
v___jp_3800_:
{
lean_object* v_s_3803_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 1, v___y_3801_);
v_s_3803_ = v___x_3798_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_stxStack_3792_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v___y_3801_);
lean_ctor_set(v_reuseFailAlloc_3807_, 2, v_pos_3793_);
lean_ctor_set(v_reuseFailAlloc_3807_, 3, v_cache_3794_);
lean_ctor_set(v_reuseFailAlloc_3807_, 4, v_errorMsg_3795_);
lean_ctor_set(v_reuseFailAlloc_3807_, 5, v_recoveredErrors_3796_);
v_s_3803_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v_startSize_3804_; 
v_startSize_3804_ = l_Lean_Parser_ParserState_stackSize(v_s_3803_);
if (lean_obj_tag(v_left_x3f_3772_) == 1)
{
lean_object* v_val_3805_; lean_object* v_s_3806_; 
v_val_3805_ = lean_ctor_get(v_left_x3f_3772_, 0);
lean_inc(v_val_3805_);
lean_dec_ref_known(v_left_x3f_3772_, 1);
v_s_3806_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3803_, v_val_3805_);
v___y_3778_ = v_startSize_3804_;
v_s_3779_ = v_s_3806_;
goto v___jp_3777_;
}
else
{
lean_dec(v_left_x3f_3772_);
v___y_3778_ = v_startSize_3804_;
v_s_3779_ = v_s_3803_;
goto v___jp_3777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3811_, lean_object* v_prio_3812_){
_start:
{
lean_object* v_pos_3813_; lean_object* v_errorMsg_3814_; lean_object* v___y_3816_; 
v_pos_3813_ = lean_ctor_get(v_s_3811_, 2);
v_errorMsg_3814_ = lean_ctor_get(v_s_3811_, 4);
if (lean_obj_tag(v_errorMsg_3814_) == 0)
{
lean_object* v___x_3819_; 
v___x_3819_ = lean_unsigned_to_nat(1u);
v___y_3816_ = v___x_3819_;
goto v___jp_3815_;
}
else
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_unsigned_to_nat(0u);
v___y_3816_ = v___x_3820_;
goto v___jp_3815_;
}
v___jp_3815_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___y_3816_);
lean_ctor_set(v___x_3817_, 1, v_prio_3812_);
lean_inc(v_pos_3813_);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v_pos_3813_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3821_, lean_object* v_prio_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3821_, v_prio_3822_);
lean_dec_ref(v_s_3821_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3824_, lean_object* v_startSize_3825_, lean_object* v_startLhsPrec_3826_, lean_object* v_startPos_3827_, lean_object* v_prevPrio_3828_, lean_object* v_prio_3829_, lean_object* v_p_3830_, lean_object* v_c_3831_, lean_object* v_s_3832_){
_start:
{
lean_object* v_lhsPrec_3833_; lean_object* v_pos_3834_; lean_object* v_errorMsg_3835_; lean_object* v_previousScore_3836_; lean_object* v_fst_3837_; lean_object* v_snd_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3894_; 
v_lhsPrec_3833_ = lean_ctor_get(v_s_3832_, 1);
lean_inc(v_lhsPrec_3833_);
v_pos_3834_ = lean_ctor_get(v_s_3832_, 2);
lean_inc(v_pos_3834_);
v_errorMsg_3835_ = lean_ctor_get(v_s_3832_, 4);
lean_inc(v_errorMsg_3835_);
lean_inc(v_prevPrio_3828_);
v_previousScore_3836_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3832_, v_prevPrio_3828_);
v_fst_3837_ = lean_ctor_get(v_previousScore_3836_, 0);
v_snd_3838_ = lean_ctor_get(v_previousScore_3836_, 1);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_previousScore_3836_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3840_ = v_previousScore_3836_;
v_isShared_3841_ = v_isSharedCheck_3894_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_snd_3838_);
lean_inc(v_fst_3837_);
lean_dec(v_previousScore_3836_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3894_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_prevSize_3842_; lean_object* v_s_3843_; lean_object* v_s_3844_; lean_object* v___x_3853_; lean_object* v_fst_3854_; lean_object* v_snd_3855_; uint8_t v___x_3856_; 
v_prevSize_3842_ = l_Lean_Parser_ParserState_stackSize(v_s_3832_);
v_s_3843_ = l_Lean_Parser_ParserState_restore(v_s_3832_, v_prevSize_3842_, v_startPos_3827_);
v_s_3844_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3824_, v_startLhsPrec_3826_, v_p_3830_, v_c_3831_, v_s_3843_);
lean_inc(v_prio_3829_);
v___x_3853_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3844_, v_prio_3829_);
v_fst_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_fst_3854_);
v_snd_3855_ = lean_ctor_get(v___x_3853_, 1);
lean_inc(v_snd_3855_);
lean_dec_ref(v___x_3853_);
v___x_3856_ = lean_nat_dec_lt(v_fst_3837_, v_fst_3854_);
if (v___x_3856_ == 0)
{
uint8_t v___x_3857_; 
v___x_3857_ = lean_nat_dec_eq(v_fst_3837_, v_fst_3854_);
lean_dec(v_fst_3854_);
lean_dec(v_fst_3837_);
if (v___x_3857_ == 0)
{
lean_dec(v_snd_3855_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_prio_3829_);
goto v___jp_3850_;
}
else
{
lean_object* v_fst_3858_; lean_object* v_snd_3859_; lean_object* v_fst_3860_; lean_object* v_snd_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3893_; 
v_fst_3858_ = lean_ctor_get(v_snd_3838_, 0);
lean_inc(v_fst_3858_);
v_snd_3859_ = lean_ctor_get(v_snd_3838_, 1);
lean_inc(v_snd_3859_);
lean_dec(v_snd_3838_);
v_fst_3860_ = lean_ctor_get(v_snd_3855_, 0);
v_snd_3861_ = lean_ctor_get(v_snd_3855_, 1);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_snd_3855_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3863_ = v_snd_3855_;
v_isShared_3864_ = v_isSharedCheck_3893_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_snd_3861_);
lean_inc(v_fst_3860_);
lean_dec(v_snd_3855_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3893_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
uint8_t v___x_3865_; 
v___x_3865_ = lean_nat_dec_lt(v_fst_3858_, v_fst_3860_);
if (v___x_3865_ == 0)
{
uint8_t v___x_3866_; 
v___x_3866_ = lean_nat_dec_eq(v_fst_3858_, v_fst_3860_);
lean_dec(v_fst_3860_);
lean_dec(v_fst_3858_);
if (v___x_3866_ == 0)
{
lean_del_object(v___x_3863_);
lean_dec(v_snd_3861_);
lean_dec(v_snd_3859_);
lean_del_object(v___x_3840_);
lean_dec(v_prio_3829_);
goto v___jp_3850_;
}
else
{
uint8_t v___x_3867_; 
v___x_3867_ = lean_nat_dec_lt(v_snd_3859_, v_snd_3861_);
if (v___x_3867_ == 0)
{
uint8_t v___x_3868_; 
lean_del_object(v___x_3840_);
v___x_3868_ = lean_nat_dec_eq(v_snd_3859_, v_snd_3861_);
lean_dec(v_snd_3861_);
lean_dec(v_snd_3859_);
if (v___x_3868_ == 0)
{
lean_del_object(v___x_3863_);
lean_dec(v_prio_3829_);
goto v___jp_3850_;
}
else
{
lean_dec(v_pos_3834_);
lean_dec(v_prevPrio_3828_);
if (lean_obj_tag(v_errorMsg_3835_) == 0)
{
lean_object* v_stxStack_3869_; lean_object* v_lhsPrec_3870_; lean_object* v_pos_3871_; lean_object* v_cache_3872_; lean_object* v_errorMsg_3873_; lean_object* v_recoveredErrors_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_prevSize_3842_);
v_stxStack_3869_ = lean_ctor_get(v_s_3844_, 0);
v_lhsPrec_3870_ = lean_ctor_get(v_s_3844_, 1);
v_pos_3871_ = lean_ctor_get(v_s_3844_, 2);
v_cache_3872_ = lean_ctor_get(v_s_3844_, 3);
v_errorMsg_3873_ = lean_ctor_get(v_s_3844_, 4);
v_recoveredErrors_3874_ = lean_ctor_get(v_s_3844_, 5);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_s_3844_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3876_ = v_s_3844_;
v_isShared_3877_ = v_isSharedCheck_3887_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_recoveredErrors_3874_);
lean_inc(v_errorMsg_3873_);
lean_inc(v_cache_3872_);
lean_inc(v_pos_3871_);
lean_inc(v_lhsPrec_3870_);
lean_inc(v_stxStack_3869_);
lean_dec(v_s_3844_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3887_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___y_3879_; uint8_t v___x_3886_; 
v___x_3886_ = lean_nat_dec_le(v_lhsPrec_3870_, v_lhsPrec_3833_);
if (v___x_3886_ == 0)
{
lean_dec(v_lhsPrec_3870_);
v___y_3879_ = v_lhsPrec_3833_;
goto v___jp_3878_;
}
else
{
lean_dec(v_lhsPrec_3833_);
v___y_3879_ = v_lhsPrec_3870_;
goto v___jp_3878_;
}
v___jp_3878_:
{
lean_object* v___x_3881_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 1, v___y_3879_);
v___x_3881_ = v___x_3876_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_stxStack_3869_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___y_3879_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_pos_3871_);
lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_cache_3872_);
lean_ctor_set(v_reuseFailAlloc_3885_, 4, v_errorMsg_3873_);
lean_ctor_set(v_reuseFailAlloc_3885_, 5, v_recoveredErrors_3874_);
v___x_3881_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3883_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 1, v_prio_3829_);
lean_ctor_set(v___x_3863_, 0, v___x_3881_);
v___x_3883_ = v___x_3863_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_prio_3829_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
else
{
lean_object* v_val_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
lean_dec(v_lhsPrec_3833_);
v_val_3888_ = lean_ctor_get(v_errorMsg_3835_, 0);
lean_inc(v_val_3888_);
lean_dec_ref_known(v_errorMsg_3835_, 1);
v___x_3889_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3844_, v_prevSize_3842_, v_val_3888_);
lean_dec(v_prevSize_3842_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 1, v_prio_3829_);
lean_ctor_set(v___x_3863_, 0, v___x_3889_);
v___x_3891_ = v___x_3863_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_prio_3829_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_del_object(v___x_3863_);
lean_dec(v_snd_3861_);
lean_dec(v_snd_3859_);
lean_dec(v_prevSize_3842_);
lean_dec(v_errorMsg_3835_);
lean_dec(v_pos_3834_);
lean_dec(v_lhsPrec_3833_);
lean_dec(v_prevPrio_3828_);
goto v___jp_3845_;
}
}
}
else
{
lean_del_object(v___x_3863_);
lean_dec(v_snd_3861_);
lean_dec(v_fst_3860_);
lean_dec(v_snd_3859_);
lean_dec(v_fst_3858_);
lean_dec(v_prevSize_3842_);
lean_dec(v_errorMsg_3835_);
lean_dec(v_pos_3834_);
lean_dec(v_lhsPrec_3833_);
lean_dec(v_prevPrio_3828_);
goto v___jp_3845_;
}
}
}
}
else
{
lean_dec(v_snd_3855_);
lean_dec(v_fst_3854_);
lean_dec(v_prevSize_3842_);
lean_dec(v_snd_3838_);
lean_dec(v_fst_3837_);
lean_dec(v_errorMsg_3835_);
lean_dec(v_pos_3834_);
lean_dec(v_lhsPrec_3833_);
lean_dec(v_prevPrio_3828_);
goto v___jp_3845_;
}
v___jp_3845_:
{
lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3846_ = l_Lean_Parser_ParserState_keepNewError(v_s_3844_, v_startSize_3825_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 1, v_prio_3829_);
lean_ctor_set(v___x_3840_, 0, v___x_3846_);
v___x_3848_ = v___x_3840_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_prio_3829_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
v___jp_3850_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3844_, v_prevSize_3842_, v_pos_3834_, v_errorMsg_3835_, v_lhsPrec_3833_);
lean_dec(v_prevSize_3842_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
lean_ctor_set(v___x_3852_, 1, v_prevPrio_3828_);
return v___x_3852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3895_, lean_object* v_startSize_3896_, lean_object* v_startLhsPrec_3897_, lean_object* v_startPos_3898_, lean_object* v_prevPrio_3899_, lean_object* v_prio_3900_, lean_object* v_p_3901_, lean_object* v_c_3902_, lean_object* v_s_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3895_, v_startSize_3896_, v_startLhsPrec_3897_, v_startPos_3898_, v_prevPrio_3899_, v_prio_3900_, v_p_3901_, v_c_3902_, v_s_3903_);
lean_dec(v_startSize_3896_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3905_, lean_object* v_s_3906_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = lean_nat_add(v_startSize_3905_, v___x_3907_);
v___x_3909_ = l_Lean_Parser_ParserState_stackSize(v_s_3906_);
v___x_3910_ = lean_nat_dec_lt(v___x_3908_, v___x_3909_);
lean_dec(v___x_3909_);
lean_dec(v___x_3908_);
if (v___x_3910_ == 0)
{
return v_s_3906_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3912_ = l_Lean_Parser_ParserState_mkNode(v_s_3906_, v___x_3911_, v_startSize_3905_);
return v___x_3912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3913_, lean_object* v_s_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3913_, v_s_3914_);
lean_dec(v_startSize_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3916_, lean_object* v_startSize_3917_, lean_object* v_startLhsPrec_3918_, lean_object* v_startPos_3919_, lean_object* v_prevPrio_3920_, lean_object* v_ps_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
if (lean_obj_tag(v_ps_3921_) == 0)
{
lean_object* v___x_3924_; 
lean_dec_ref(v_a_3922_);
lean_dec(v_prevPrio_3920_);
lean_dec(v_startPos_3919_);
lean_dec(v_startLhsPrec_3918_);
lean_dec(v_left_x3f_3916_);
v___x_3924_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3917_, v_a_3923_);
return v___x_3924_;
}
else
{
lean_object* v_head_3925_; lean_object* v_fst_3926_; lean_object* v_tail_3927_; lean_object* v_snd_3928_; lean_object* v_fn_3929_; lean_object* v___x_3930_; lean_object* v_fst_3931_; lean_object* v_snd_3932_; 
v_head_3925_ = lean_ctor_get(v_ps_3921_, 0);
lean_inc(v_head_3925_);
v_fst_3926_ = lean_ctor_get(v_head_3925_, 0);
lean_inc(v_fst_3926_);
v_tail_3927_ = lean_ctor_get(v_ps_3921_, 1);
lean_inc(v_tail_3927_);
lean_dec_ref_known(v_ps_3921_, 2);
v_snd_3928_ = lean_ctor_get(v_head_3925_, 1);
lean_inc(v_snd_3928_);
lean_dec(v_head_3925_);
v_fn_3929_ = lean_ctor_get(v_fst_3926_, 1);
lean_inc_ref(v_fn_3929_);
lean_dec(v_fst_3926_);
lean_inc_ref(v_a_3922_);
lean_inc(v_startPos_3919_);
lean_inc(v_startLhsPrec_3918_);
lean_inc(v_left_x3f_3916_);
v___x_3930_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3916_, v_startSize_3917_, v_startLhsPrec_3918_, v_startPos_3919_, v_prevPrio_3920_, v_snd_3928_, v_fn_3929_, v_a_3922_, v_a_3923_);
v_fst_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_fst_3931_);
v_snd_3932_ = lean_ctor_get(v___x_3930_, 1);
lean_inc(v_snd_3932_);
lean_dec_ref(v___x_3930_);
v_prevPrio_3920_ = v_snd_3932_;
v_ps_3921_ = v_tail_3927_;
v_a_3923_ = v_fst_3931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3934_, lean_object* v_startSize_3935_, lean_object* v_startLhsPrec_3936_, lean_object* v_startPos_3937_, lean_object* v_prevPrio_3938_, lean_object* v_ps_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3934_, v_startSize_3935_, v_startLhsPrec_3936_, v_startPos_3937_, v_prevPrio_3938_, v_ps_3939_, v_a_3940_, v_a_3941_);
lean_dec(v_startSize_3935_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3943_, lean_object* v_startSize_3944_, lean_object* v_startLhsPrec_3945_, lean_object* v_startPos_3946_, lean_object* v_prevPrio_3947_, lean_object* v_ps_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3943_, v_startSize_3944_, v_startLhsPrec_3945_, v_startPos_3946_, v_prevPrio_3947_, v_ps_3948_, v_a_3949_, v_a_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3952_, lean_object* v_startSize_3953_, lean_object* v_startLhsPrec_3954_, lean_object* v_startPos_3955_, lean_object* v_prevPrio_3956_, lean_object* v_ps_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3952_, v_startSize_3953_, v_startLhsPrec_3954_, v_startPos_3955_, v_prevPrio_3956_, v_ps_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_startSize_3953_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3962_, lean_object* v_x_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
if (lean_obj_tag(v_x_3963_) == 0)
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec_ref(v_a_3964_);
lean_dec(v_left_x3f_3962_);
v___x_3966_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3967_ = l_Lean_Parser_ParserState_mkError(v_a_3965_, v___x_3966_);
return v___x_3967_;
}
else
{
lean_object* v_tail_3968_; 
v_tail_3968_ = lean_ctor_get(v_x_3963_, 1);
if (lean_obj_tag(v_tail_3968_) == 0)
{
lean_object* v_head_3969_; lean_object* v_fst_3970_; lean_object* v_lhsPrec_3971_; lean_object* v_fn_3972_; lean_object* v___x_3973_; 
v_head_3969_ = lean_ctor_get(v_x_3963_, 0);
lean_inc(v_head_3969_);
lean_dec_ref_known(v_x_3963_, 2);
v_fst_3970_ = lean_ctor_get(v_head_3969_, 0);
lean_inc(v_fst_3970_);
lean_dec(v_head_3969_);
v_lhsPrec_3971_ = lean_ctor_get(v_a_3965_, 1);
lean_inc(v_lhsPrec_3971_);
v_fn_3972_ = lean_ctor_get(v_fst_3970_, 1);
lean_inc_ref(v_fn_3972_);
lean_dec(v_fst_3970_);
v___x_3973_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3962_, v_lhsPrec_3971_, v_fn_3972_, v_a_3964_, v_a_3965_);
return v___x_3973_;
}
else
{
lean_object* v_head_3974_; lean_object* v_fst_3975_; lean_object* v_lhsPrec_3976_; lean_object* v_pos_3977_; lean_object* v_snd_3978_; lean_object* v_fn_3979_; lean_object* v_startSize_3980_; lean_object* v_s_3981_; lean_object* v___x_3982_; 
lean_inc(v_tail_3968_);
v_head_3974_ = lean_ctor_get(v_x_3963_, 0);
lean_inc(v_head_3974_);
lean_dec_ref_known(v_x_3963_, 2);
v_fst_3975_ = lean_ctor_get(v_head_3974_, 0);
lean_inc(v_fst_3975_);
v_lhsPrec_3976_ = lean_ctor_get(v_a_3965_, 1);
lean_inc_n(v_lhsPrec_3976_, 2);
v_pos_3977_ = lean_ctor_get(v_a_3965_, 2);
lean_inc(v_pos_3977_);
v_snd_3978_ = lean_ctor_get(v_head_3974_, 1);
lean_inc(v_snd_3978_);
lean_dec(v_head_3974_);
v_fn_3979_ = lean_ctor_get(v_fst_3975_, 1);
lean_inc_ref(v_fn_3979_);
lean_dec(v_fst_3975_);
v_startSize_3980_ = l_Lean_Parser_ParserState_stackSize(v_a_3965_);
lean_inc_ref(v_a_3964_);
lean_inc(v_left_x3f_3962_);
v_s_3981_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3962_, v_lhsPrec_3976_, v_fn_3979_, v_a_3964_, v_a_3965_);
v___x_3982_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3962_, v_startSize_3980_, v_lhsPrec_3976_, v_pos_3977_, v_snd_3978_, v_tail_3968_, v_a_3964_, v_s_3981_);
lean_dec(v_startSize_3980_);
return v___x_3982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_dec_ref(v_x_3985_);
v___x_3987_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_3988_ = l_Lean_Parser_ParserState_mkError(v_x_3986_, v___x_3987_);
return v___x_3988_;
}
else
{
lean_object* v_tail_3989_; 
v_tail_3989_ = lean_ctor_get(v_x_3984_, 1);
if (lean_obj_tag(v_tail_3989_) == 0)
{
lean_object* v_head_3990_; lean_object* v_fn_3991_; lean_object* v___x_3992_; 
v_head_3990_ = lean_ctor_get(v_x_3984_, 0);
lean_inc(v_head_3990_);
lean_dec_ref_known(v_x_3984_, 2);
v_fn_3991_ = lean_ctor_get(v_head_3990_, 1);
lean_inc_ref(v_fn_3991_);
lean_dec(v_head_3990_);
v___x_3992_ = lean_apply_2(v_fn_3991_, v_x_3985_, v_x_3986_);
return v___x_3992_;
}
else
{
lean_object* v_head_3993_; lean_object* v_fn_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_inc(v_tail_3989_);
v_head_3993_ = lean_ctor_get(v_x_3984_, 0);
lean_inc(v_head_3993_);
lean_dec_ref_known(v_x_3984_, 2);
v_fn_3994_ = lean_ctor_get(v_head_3993_, 1);
lean_inc_ref(v_fn_3994_);
lean_dec(v_head_3993_);
v___x_3995_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_3995_, 0, v_tail_3989_);
v___x_3996_ = l_Lean_Parser_orelseFn(v_fn_3994_, v___x_3995_, v_x_3985_, v_x_3986_);
return v___x_3996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_3997_, lean_object* v_c_3998_, lean_object* v_s_3999_){
_start:
{
lean_object* v_toCacheableParserContext_4000_; lean_object* v_savedPos_x3f_4001_; 
v_toCacheableParserContext_4000_ = lean_ctor_get(v_c_3998_, 2);
v_savedPos_x3f_4001_ = lean_ctor_get(v_toCacheableParserContext_4000_, 2);
lean_inc(v_savedPos_x3f_4001_);
if (lean_obj_tag(v_savedPos_x3f_4001_) == 0)
{
lean_dec_ref(v_c_3998_);
lean_dec_ref(v_errorMsg_3997_);
return v_s_3999_;
}
else
{
lean_object* v_toInputContext_4002_; lean_object* v_val_4003_; lean_object* v_fileMap_4004_; lean_object* v_pos_4005_; lean_object* v_savedPos_4006_; lean_object* v_pos_4007_; lean_object* v_column_4008_; lean_object* v_column_4009_; uint8_t v___x_4010_; 
v_toInputContext_4002_ = lean_ctor_get(v_c_3998_, 0);
lean_inc_ref(v_toInputContext_4002_);
lean_dec_ref(v_c_3998_);
v_val_4003_ = lean_ctor_get(v_savedPos_x3f_4001_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v_savedPos_x3f_4001_, 1);
v_fileMap_4004_ = lean_ctor_get(v_toInputContext_4002_, 2);
lean_inc_ref_n(v_fileMap_4004_, 2);
lean_dec_ref(v_toInputContext_4002_);
v_pos_4005_ = lean_ctor_get(v_s_3999_, 2);
v_savedPos_4006_ = l_Lean_FileMap_toPosition(v_fileMap_4004_, v_val_4003_);
lean_dec(v_val_4003_);
v_pos_4007_ = l_Lean_FileMap_toPosition(v_fileMap_4004_, v_pos_4005_);
v_column_4008_ = lean_ctor_get(v_pos_4007_, 1);
lean_inc(v_column_4008_);
lean_dec_ref(v_pos_4007_);
v_column_4009_ = lean_ctor_get(v_savedPos_4006_, 1);
lean_inc(v_column_4009_);
lean_dec_ref(v_savedPos_4006_);
v___x_4010_ = lean_nat_dec_eq(v_column_4008_, v_column_4009_);
lean_dec(v_column_4009_);
lean_dec(v_column_4008_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Parser_ParserState_mkError(v_s_3999_, v_errorMsg_3997_);
return v___x_4011_;
}
else
{
lean_dec_ref(v_errorMsg_3997_);
return v_s_3999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_4012_){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4013_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4014_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_4014_, 0, v_errorMsg_4012_);
v___x_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4024_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4025_ = l_Lean_addBuiltinDocString(v___x_4023_, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4028_, lean_object* v_c_4029_, lean_object* v_s_4030_){
_start:
{
lean_object* v_toCacheableParserContext_4031_; lean_object* v_savedPos_x3f_4032_; 
v_toCacheableParserContext_4031_ = lean_ctor_get(v_c_4029_, 2);
v_savedPos_x3f_4032_ = lean_ctor_get(v_toCacheableParserContext_4031_, 2);
lean_inc(v_savedPos_x3f_4032_);
if (lean_obj_tag(v_savedPos_x3f_4032_) == 0)
{
lean_dec_ref(v_c_4029_);
lean_dec_ref(v_errorMsg_4028_);
return v_s_4030_;
}
else
{
lean_object* v_toInputContext_4033_; lean_object* v_val_4034_; lean_object* v_fileMap_4035_; lean_object* v_pos_4036_; lean_object* v_savedPos_4037_; lean_object* v_column_4038_; lean_object* v_pos_4039_; lean_object* v_column_4040_; uint8_t v___x_4041_; 
v_toInputContext_4033_ = lean_ctor_get(v_c_4029_, 0);
lean_inc_ref(v_toInputContext_4033_);
lean_dec_ref(v_c_4029_);
v_val_4034_ = lean_ctor_get(v_savedPos_x3f_4032_, 0);
lean_inc(v_val_4034_);
lean_dec_ref_known(v_savedPos_x3f_4032_, 1);
v_fileMap_4035_ = lean_ctor_get(v_toInputContext_4033_, 2);
lean_inc_ref_n(v_fileMap_4035_, 2);
lean_dec_ref(v_toInputContext_4033_);
v_pos_4036_ = lean_ctor_get(v_s_4030_, 2);
v_savedPos_4037_ = l_Lean_FileMap_toPosition(v_fileMap_4035_, v_val_4034_);
lean_dec(v_val_4034_);
v_column_4038_ = lean_ctor_get(v_savedPos_4037_, 1);
lean_inc(v_column_4038_);
lean_dec_ref(v_savedPos_4037_);
v_pos_4039_ = l_Lean_FileMap_toPosition(v_fileMap_4035_, v_pos_4036_);
v_column_4040_ = lean_ctor_get(v_pos_4039_, 1);
lean_inc(v_column_4040_);
lean_dec_ref(v_pos_4039_);
v___x_4041_ = lean_nat_dec_le(v_column_4038_, v_column_4040_);
lean_dec(v_column_4040_);
lean_dec(v_column_4038_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Parser_ParserState_mkError(v_s_4030_, v_errorMsg_4028_);
return v___x_4042_;
}
else
{
lean_dec_ref(v_errorMsg_4028_);
return v_s_4030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4043_){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4045_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4045_, 0, v_errorMsg_4043_);
v___x_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4054_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4055_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4056_ = l_Lean_addBuiltinDocString(v___x_4054_, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4059_, lean_object* v_c_4060_, lean_object* v_s_4061_){
_start:
{
lean_object* v_toCacheableParserContext_4062_; lean_object* v_savedPos_x3f_4063_; 
v_toCacheableParserContext_4062_ = lean_ctor_get(v_c_4060_, 2);
v_savedPos_x3f_4063_ = lean_ctor_get(v_toCacheableParserContext_4062_, 2);
lean_inc(v_savedPos_x3f_4063_);
if (lean_obj_tag(v_savedPos_x3f_4063_) == 0)
{
lean_dec_ref(v_c_4060_);
lean_dec_ref(v_errorMsg_4059_);
return v_s_4061_;
}
else
{
lean_object* v_toInputContext_4064_; lean_object* v_val_4065_; lean_object* v_fileMap_4066_; lean_object* v_pos_4067_; lean_object* v_savedPos_4068_; lean_object* v_column_4069_; lean_object* v_pos_4070_; lean_object* v_column_4071_; uint8_t v___x_4072_; 
v_toInputContext_4064_ = lean_ctor_get(v_c_4060_, 0);
lean_inc_ref(v_toInputContext_4064_);
lean_dec_ref(v_c_4060_);
v_val_4065_ = lean_ctor_get(v_savedPos_x3f_4063_, 0);
lean_inc(v_val_4065_);
lean_dec_ref_known(v_savedPos_x3f_4063_, 1);
v_fileMap_4066_ = lean_ctor_get(v_toInputContext_4064_, 2);
lean_inc_ref_n(v_fileMap_4066_, 2);
lean_dec_ref(v_toInputContext_4064_);
v_pos_4067_ = lean_ctor_get(v_s_4061_, 2);
v_savedPos_4068_ = l_Lean_FileMap_toPosition(v_fileMap_4066_, v_val_4065_);
lean_dec(v_val_4065_);
v_column_4069_ = lean_ctor_get(v_savedPos_4068_, 1);
lean_inc(v_column_4069_);
lean_dec_ref(v_savedPos_4068_);
v_pos_4070_ = l_Lean_FileMap_toPosition(v_fileMap_4066_, v_pos_4067_);
v_column_4071_ = lean_ctor_get(v_pos_4070_, 1);
lean_inc(v_column_4071_);
lean_dec_ref(v_pos_4070_);
v___x_4072_ = lean_nat_dec_lt(v_column_4069_, v_column_4071_);
lean_dec(v_column_4071_);
lean_dec(v_column_4069_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_Parser_ParserState_mkError(v_s_4061_, v_errorMsg_4059_);
return v___x_4073_;
}
else
{
lean_dec_ref(v_errorMsg_4059_);
return v_s_4061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4074_){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4076_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4076_, 0, v_errorMsg_4074_);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4075_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4086_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4087_ = l_Lean_addBuiltinDocString(v___x_4085_, v___x_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4090_, lean_object* v_c_4091_, lean_object* v_s_4092_){
_start:
{
lean_object* v_toCacheableParserContext_4093_; lean_object* v_savedPos_x3f_4094_; 
v_toCacheableParserContext_4093_ = lean_ctor_get(v_c_4091_, 2);
v_savedPos_x3f_4094_ = lean_ctor_get(v_toCacheableParserContext_4093_, 2);
lean_inc(v_savedPos_x3f_4094_);
if (lean_obj_tag(v_savedPos_x3f_4094_) == 0)
{
lean_dec_ref(v_c_4091_);
lean_dec_ref(v_errorMsg_4090_);
return v_s_4092_;
}
else
{
lean_object* v_toInputContext_4095_; lean_object* v_val_4096_; lean_object* v_fileMap_4097_; lean_object* v_pos_4098_; lean_object* v_savedPos_4099_; lean_object* v_pos_4100_; lean_object* v_line_4101_; lean_object* v_line_4102_; uint8_t v___x_4103_; 
v_toInputContext_4095_ = lean_ctor_get(v_c_4091_, 0);
lean_inc_ref(v_toInputContext_4095_);
lean_dec_ref(v_c_4091_);
v_val_4096_ = lean_ctor_get(v_savedPos_x3f_4094_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v_savedPos_x3f_4094_, 1);
v_fileMap_4097_ = lean_ctor_get(v_toInputContext_4095_, 2);
lean_inc_ref_n(v_fileMap_4097_, 2);
lean_dec_ref(v_toInputContext_4095_);
v_pos_4098_ = lean_ctor_get(v_s_4092_, 2);
v_savedPos_4099_ = l_Lean_FileMap_toPosition(v_fileMap_4097_, v_val_4096_);
lean_dec(v_val_4096_);
v_pos_4100_ = l_Lean_FileMap_toPosition(v_fileMap_4097_, v_pos_4098_);
v_line_4101_ = lean_ctor_get(v_pos_4100_, 0);
lean_inc(v_line_4101_);
lean_dec_ref(v_pos_4100_);
v_line_4102_ = lean_ctor_get(v_savedPos_4099_, 0);
lean_inc(v_line_4102_);
lean_dec_ref(v_savedPos_4099_);
v___x_4103_ = lean_nat_dec_eq(v_line_4101_, v_line_4102_);
lean_dec(v_line_4102_);
lean_dec(v_line_4101_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Lean_Parser_ParserState_mkError(v_s_4092_, v_errorMsg_4090_);
return v___x_4104_;
}
else
{
lean_dec_ref(v_errorMsg_4090_);
return v_s_4092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4105_){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4107_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4107_, 0, v_errorMsg_4105_);
v___x_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4117_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4118_ = l_Lean_addBuiltinDocString(v___x_4116_, v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4121_, lean_object* v_x_4122_){
_start:
{
lean_object* v_prec_4123_; lean_object* v_quotDepth_4124_; uint8_t v_suppressInsideQuot_4125_; lean_object* v_forbiddenTks_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4135_; 
v_prec_4123_ = lean_ctor_get(v_x_4122_, 0);
v_quotDepth_4124_ = lean_ctor_get(v_x_4122_, 1);
v_suppressInsideQuot_4125_ = lean_ctor_get_uint8(v_x_4122_, sizeof(void*)*4);
v_forbiddenTks_4126_ = lean_ctor_get(v_x_4122_, 3);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_x_4122_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; 
v_unused_4136_ = lean_ctor_get(v_x_4122_, 2);
lean_dec(v_unused_4136_);
v___x_4128_ = v_x_4122_;
v_isShared_4129_ = v_isSharedCheck_4135_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_forbiddenTks_4126_);
lean_inc(v_quotDepth_4124_);
lean_inc(v_prec_4123_);
lean_dec(v_x_4122_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4135_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_pos_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v_pos_4130_ = lean_ctor_get(v___y_4121_, 2);
lean_inc(v_pos_4130_);
v___x_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4131_, 0, v_pos_4130_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 2, v___x_4131_);
v___x_4133_ = v___x_4128_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_prec_4123_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_quotDepth_4124_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v___x_4131_);
lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_forbiddenTks_4126_);
lean_ctor_set_uint8(v_reuseFailAlloc_4134_, sizeof(void*)*4, v_suppressInsideQuot_4125_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4137_, lean_object* v_x_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Parser_withPosition___lam__0(v___y_4137_, v_x_4138_);
lean_dec_ref(v___y_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___f_4143_; lean_object* v___x_4144_; 
lean_inc_ref(v___y_4142_);
v___f_4143_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4143_, 0, v___y_4142_);
v___x_4144_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4143_, v_fn_4140_, v___y_4141_, v___y_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4145_){
_start:
{
lean_object* v_info_4146_; lean_object* v_fn_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4155_; 
v_info_4146_ = lean_ctor_get(v_p_4145_, 0);
v_fn_4147_ = lean_ctor_get(v_p_4145_, 1);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_p_4145_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4149_ = v_p_4145_;
v_isShared_4150_ = v_isSharedCheck_4155_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_fn_4147_);
lean_inc(v_info_4146_);
lean_dec(v_p_4145_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4155_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___f_4151_; lean_object* v___x_4153_; 
v___f_4151_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4151_, 0, v_fn_4147_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 1, v___f_4151_);
v___x_4153_ = v___x_4149_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_info_4146_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v___f_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4164_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4165_ = l_Lean_addBuiltinDocString(v___x_4163_, v___x_4164_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4168_, lean_object* v_pos_4169_, lean_object* v_c_4170_){
_start:
{
uint8_t v___x_4171_; 
v___x_4171_ = l_Lean_Parser_checkTailLinebreak(v_prev_4168_);
if (v___x_4171_ == 0)
{
lean_dec(v_pos_4169_);
return v_c_4170_;
}
else
{
lean_object* v_prec_4172_; lean_object* v_quotDepth_4173_; uint8_t v_suppressInsideQuot_4174_; lean_object* v_forbiddenTks_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4183_; 
v_prec_4172_ = lean_ctor_get(v_c_4170_, 0);
v_quotDepth_4173_ = lean_ctor_get(v_c_4170_, 1);
v_suppressInsideQuot_4174_ = lean_ctor_get_uint8(v_c_4170_, sizeof(void*)*4);
v_forbiddenTks_4175_ = lean_ctor_get(v_c_4170_, 3);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_c_4170_);
if (v_isSharedCheck_4183_ == 0)
{
lean_object* v_unused_4184_; 
v_unused_4184_ = lean_ctor_get(v_c_4170_, 2);
lean_dec(v_unused_4184_);
v___x_4177_ = v_c_4170_;
v_isShared_4178_ = v_isSharedCheck_4183_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_forbiddenTks_4175_);
lean_inc(v_quotDepth_4173_);
lean_inc(v_prec_4172_);
lean_dec(v_c_4170_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4183_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4179_; lean_object* v___x_4181_; 
v___x_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_pos_4169_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 2, v___x_4179_);
v___x_4181_ = v___x_4177_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_prec_4172_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_quotDepth_4173_);
lean_ctor_set(v_reuseFailAlloc_4182_, 2, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4182_, 3, v_forbiddenTks_4175_);
lean_ctor_set_uint8(v_reuseFailAlloc_4182_, sizeof(void*)*4, v_suppressInsideQuot_4174_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4185_, lean_object* v_pos_4186_, lean_object* v_c_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4185_, v_pos_4186_, v_c_4187_);
lean_dec(v_prev_4185_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v_stxStack_4192_; lean_object* v_pos_4193_; lean_object* v_prev_4194_; lean_object* v___f_4195_; lean_object* v___x_4196_; 
v_stxStack_4192_ = lean_ctor_get(v___y_4191_, 0);
v_pos_4193_ = lean_ctor_get(v___y_4191_, 2);
v_prev_4194_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4192_);
lean_inc(v_pos_4193_);
v___f_4195_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4195_, 0, v_prev_4194_);
lean_closure_set(v___f_4195_, 1, v_pos_4193_);
v___x_4196_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4195_, v_fn_4189_, v___y_4190_, v___y_4191_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4197_){
_start:
{
lean_object* v_info_4198_; lean_object* v_fn_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4207_; 
v_info_4198_ = lean_ctor_get(v_p_4197_, 0);
v_fn_4199_ = lean_ctor_get(v_p_4197_, 1);
v_isSharedCheck_4207_ = !lean_is_exclusive(v_p_4197_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4201_ = v_p_4197_;
v_isShared_4202_ = v_isSharedCheck_4207_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_fn_4199_);
lean_inc(v_info_4198_);
lean_dec(v_p_4197_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4207_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___f_4203_; lean_object* v___x_4205_; 
v___f_4203_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4203_, 0, v_fn_4199_);
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 1, v___f_4203_);
v___x_4205_ = v___x_4201_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_info_4198_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v___f_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4208_){
_start:
{
lean_object* v_prec_4209_; lean_object* v_quotDepth_4210_; uint8_t v_suppressInsideQuot_4211_; lean_object* v_forbiddenTks_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4220_; 
v_prec_4209_ = lean_ctor_get(v_x_4208_, 0);
v_quotDepth_4210_ = lean_ctor_get(v_x_4208_, 1);
v_suppressInsideQuot_4211_ = lean_ctor_get_uint8(v_x_4208_, sizeof(void*)*4);
v_forbiddenTks_4212_ = lean_ctor_get(v_x_4208_, 3);
v_isSharedCheck_4220_ = !lean_is_exclusive(v_x_4208_);
if (v_isSharedCheck_4220_ == 0)
{
lean_object* v_unused_4221_; 
v_unused_4221_ = lean_ctor_get(v_x_4208_, 2);
lean_dec(v_unused_4221_);
v___x_4214_ = v_x_4208_;
v_isShared_4215_ = v_isSharedCheck_4220_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_forbiddenTks_4212_);
lean_inc(v_quotDepth_4210_);
lean_inc(v_prec_4209_);
lean_dec(v_x_4208_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4220_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4218_; 
v___x_4216_ = lean_box(0);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 2, v___x_4216_);
v___x_4218_ = v___x_4214_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_prec_4209_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_quotDepth_4210_);
lean_ctor_set(v_reuseFailAlloc_4219_, 2, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4219_, 3, v_forbiddenTks_4212_);
lean_ctor_set_uint8(v_reuseFailAlloc_4219_, sizeof(void*)*4, v_suppressInsideQuot_4211_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4223_){
_start:
{
lean_object* v___f_4224_; lean_object* v___x_4225_; 
v___f_4224_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4225_ = l_Lean_Parser_adaptCacheableContext(v___f_4224_, v_p_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4233_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4234_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4235_ = l_Lean_addBuiltinDocString(v___x_4233_, v___x_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4238_, lean_object* v_c_4239_){
_start:
{
lean_object* v_prec_4240_; lean_object* v_quotDepth_4241_; uint8_t v_suppressInsideQuot_4242_; lean_object* v_savedPos_x3f_4243_; lean_object* v_forbiddenTks_4244_; uint8_t v___x_4245_; 
v_prec_4240_ = lean_ctor_get(v_c_4239_, 0);
v_quotDepth_4241_ = lean_ctor_get(v_c_4239_, 1);
v_suppressInsideQuot_4242_ = lean_ctor_get_uint8(v_c_4239_, sizeof(void*)*4);
v_savedPos_x3f_4243_ = lean_ctor_get(v_c_4239_, 2);
v_forbiddenTks_4244_ = lean_ctor_get(v_c_4239_, 3);
v___x_4245_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_4244_, v_tk_4238_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4253_; 
lean_inc_ref(v_forbiddenTks_4244_);
lean_inc(v_savedPos_x3f_4243_);
lean_inc(v_quotDepth_4241_);
lean_inc(v_prec_4240_);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_c_4239_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; lean_object* v_unused_4255_; lean_object* v_unused_4256_; lean_object* v_unused_4257_; 
v_unused_4254_ = lean_ctor_get(v_c_4239_, 3);
lean_dec(v_unused_4254_);
v_unused_4255_ = lean_ctor_get(v_c_4239_, 2);
lean_dec(v_unused_4255_);
v_unused_4256_ = lean_ctor_get(v_c_4239_, 1);
lean_dec(v_unused_4256_);
v_unused_4257_ = lean_ctor_get(v_c_4239_, 0);
lean_dec(v_unused_4257_);
v___x_4247_ = v_c_4239_;
v_isShared_4248_ = v_isSharedCheck_4253_;
goto v_resetjp_4246_;
}
else
{
lean_dec(v_c_4239_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4253_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4249_ = lean_array_push(v_forbiddenTks_4244_, v_tk_4238_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 3, v___x_4249_);
v___x_4251_ = v___x_4247_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_prec_4240_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_quotDepth_4241_);
lean_ctor_set(v_reuseFailAlloc_4252_, 2, v_savedPos_x3f_4243_);
lean_ctor_set(v_reuseFailAlloc_4252_, 3, v___x_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4252_, sizeof(void*)*4, v_suppressInsideQuot_4242_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
else
{
lean_dec_ref(v_tk_4238_);
return v_c_4239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4258_, lean_object* v_p_4259_){
_start:
{
lean_object* v___f_4260_; lean_object* v___x_4261_; 
v___f_4260_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4260_, 0, v_tk_4258_);
v___x_4261_ = l_Lean_Parser_adaptCacheableContext(v___f_4260_, v_p_4259_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4269_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4270_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4271_ = l_Lean_addBuiltinDocString(v___x_4269_, v___x_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4273_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(lean_object* v_a_4274_, lean_object* v_as_4275_, size_t v_i_4276_, size_t v_stop_4277_){
_start:
{
uint8_t v___x_4278_; 
v___x_4278_ = lean_usize_dec_eq(v_i_4276_, v_stop_4277_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4279_ = lean_array_uget_borrowed(v_as_4275_, v_i_4276_);
v___x_4280_ = lean_string_dec_eq(v___x_4279_, v_a_4274_);
if (v___x_4280_ == 0)
{
size_t v___x_4281_; size_t v___x_4282_; 
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_add(v_i_4276_, v___x_4281_);
v_i_4276_ = v___x_4282_;
goto _start;
}
else
{
return v___x_4280_;
}
}
else
{
uint8_t v___x_4284_; 
v___x_4284_ = 0;
return v___x_4284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0___boxed(lean_object* v_a_4285_, lean_object* v_as_4286_, lean_object* v_i_4287_, lean_object* v_stop_4288_){
_start:
{
size_t v_i_boxed_4289_; size_t v_stop_boxed_4290_; uint8_t v_res_4291_; lean_object* v_r_4292_; 
v_i_boxed_4289_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_stop_boxed_4290_ = lean_unbox_usize(v_stop_4288_);
lean_dec(v_stop_4288_);
v_res_4291_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4285_, v_as_4286_, v_i_boxed_4289_, v_stop_boxed_4290_);
lean_dec_ref(v_as_4286_);
lean_dec_ref(v_a_4285_);
v_r_4292_ = lean_box(v_res_4291_);
return v_r_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(lean_object* v_size_4293_, lean_object* v_as_4294_, size_t v_sz_4295_, size_t v_i_4296_, lean_object* v_b_4297_){
_start:
{
lean_object* v_a_4299_; uint8_t v___x_4303_; 
v___x_4303_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
if (v___x_4303_ == 0)
{
lean_dec(v_size_4293_);
return v_b_4297_;
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4307_; lean_object* v___y_4309_; uint8_t v___x_4314_; 
v_a_4304_ = lean_array_uget_borrowed(v_as_4294_, v_i_4296_);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4314_ = lean_nat_dec_lt(v___x_4307_, v_size_4293_);
if (v___x_4314_ == 0)
{
goto v___jp_4305_;
}
else
{
lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4315_ = lean_array_get_size(v_b_4297_);
v___x_4316_ = lean_nat_dec_le(v_size_4293_, v___x_4315_);
if (v___x_4316_ == 0)
{
v___y_4309_ = v___x_4315_;
goto v___jp_4308_;
}
else
{
lean_inc(v_size_4293_);
v___y_4309_ = v_size_4293_;
goto v___jp_4308_;
}
}
v___jp_4305_:
{
lean_object* v___x_4306_; 
lean_inc(v_a_4304_);
v___x_4306_ = lean_array_push(v_b_4297_, v_a_4304_);
v_a_4299_ = v___x_4306_;
goto v___jp_4298_;
}
v___jp_4308_:
{
uint8_t v___x_4310_; 
v___x_4310_ = lean_nat_dec_lt(v___x_4307_, v___y_4309_);
if (v___x_4310_ == 0)
{
lean_dec(v___y_4309_);
goto v___jp_4305_;
}
else
{
size_t v___x_4311_; size_t v___x_4312_; uint8_t v___x_4313_; 
v___x_4311_ = ((size_t)0ULL);
v___x_4312_ = lean_usize_of_nat(v___y_4309_);
lean_dec(v___y_4309_);
v___x_4313_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4304_, v_b_4297_, v___x_4311_, v___x_4312_);
if (v___x_4313_ == 0)
{
goto v___jp_4305_;
}
else
{
v_a_4299_ = v_b_4297_;
goto v___jp_4298_;
}
}
}
}
v___jp_4298_:
{
size_t v___x_4300_; size_t v___x_4301_; 
v___x_4300_ = ((size_t)1ULL);
v___x_4301_ = lean_usize_add(v_i_4296_, v___x_4300_);
v_i_4296_ = v___x_4301_;
v_b_4297_ = v_a_4299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1___boxed(lean_object* v_size_4317_, lean_object* v_as_4318_, lean_object* v_sz_4319_, lean_object* v_i_4320_, lean_object* v_b_4321_){
_start:
{
size_t v_sz_boxed_4322_; size_t v_i_boxed_4323_; lean_object* v_res_4324_; 
v_sz_boxed_4322_ = lean_unbox_usize(v_sz_4319_);
lean_dec(v_sz_4319_);
v_i_boxed_4323_ = lean_unbox_usize(v_i_4320_);
lean_dec(v_i_4320_);
v_res_4324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4317_, v_as_4318_, v_sz_boxed_4322_, v_i_boxed_4323_, v_b_4321_);
lean_dec_ref(v_as_4318_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(lean_object* v_init_4325_, lean_object* v_tks_4326_){
_start:
{
lean_object* v_size_4327_; size_t v_sz_4328_; size_t v___x_4329_; lean_object* v___x_4330_; 
v_size_4327_ = lean_array_get_size(v_init_4325_);
v_sz_4328_ = lean_array_size(v_tks_4326_);
v___x_4329_ = ((size_t)0ULL);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4327_, v_tks_4326_, v_sz_4328_, v___x_4329_, v_init_4325_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks___boxed(lean_object* v_init_4331_, lean_object* v_tks_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_init_4331_, v_tks_4332_);
lean_dec_ref(v_tks_4332_);
return v_res_4333_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__6));
v___x_4356_ = l_Lean_mkAtom(v___x_4355_);
return v___x_4356_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4357_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__8, &l_Lean_Parser_withForbiddens___auto__1___closed__8_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__8);
v___x_4358_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4359_ = lean_array_push(v___x_4358_, v___x_4357_);
return v___x_4359_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4370_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_4371_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4372_ = lean_array_push(v___x_4371_, v___x_4370_);
return v___x_4372_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4373_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__13, &l_Lean_Parser_withForbiddens___auto__1___closed__13_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__13);
v___x_4374_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__11));
v___x_4375_ = lean_box(2);
v___x_4376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
lean_ctor_set(v___x_4376_, 1, v___x_4374_);
lean_ctor_set(v___x_4376_, 2, v___x_4373_);
return v___x_4376_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4377_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__14, &l_Lean_Parser_withForbiddens___auto__1___closed__14_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__14);
v___x_4378_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__9, &l_Lean_Parser_withForbiddens___auto__1___closed__9_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__9);
v___x_4379_ = lean_array_push(v___x_4378_, v___x_4377_);
return v___x_4379_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4380_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__15, &l_Lean_Parser_withForbiddens___auto__1___closed__15_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__15);
v___x_4381_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__7));
v___x_4382_ = lean_box(2);
v___x_4383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v___x_4381_);
lean_ctor_set(v___x_4383_, 2, v___x_4380_);
return v___x_4383_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4384_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__16, &l_Lean_Parser_withForbiddens___auto__1___closed__16_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__16);
v___x_4385_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4386_ = lean_array_push(v___x_4385_, v___x_4384_);
return v___x_4386_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4387_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__17, &l_Lean_Parser_withForbiddens___auto__1___closed__17_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__17);
v___x_4388_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_4389_ = lean_box(2);
v___x_4390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___x_4388_);
lean_ctor_set(v___x_4390_, 2, v___x_4387_);
return v___x_4390_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4391_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__18, &l_Lean_Parser_withForbiddens___auto__1___closed__18_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__18);
v___x_4392_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4393_ = lean_array_push(v___x_4392_, v___x_4391_);
return v___x_4393_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4394_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__19, &l_Lean_Parser_withForbiddens___auto__1___closed__19_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__19);
v___x_4395_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__5));
v___x_4396_ = lean_box(2);
v___x_4397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___x_4395_);
lean_ctor_set(v___x_4397_, 2, v___x_4394_);
return v___x_4397_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__20, &l_Lean_Parser_withForbiddens___auto__1___closed__20_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__20);
v___x_4399_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4400_ = lean_array_push(v___x_4399_, v___x_4398_);
return v___x_4400_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4401_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__21, &l_Lean_Parser_withForbiddens___auto__1___closed__21_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__21);
v___x_4402_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__2));
v___x_4403_ = lean_box(2);
v___x_4404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v___x_4402_);
lean_ctor_set(v___x_4404_, 2, v___x_4401_);
return v___x_4404_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1(void){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__22, &l_Lean_Parser_withForbiddens___auto__1___closed__22_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__22);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg___lam__0(lean_object* v_tks_4406_, lean_object* v_c_4407_){
_start:
{
lean_object* v_prec_4408_; lean_object* v_quotDepth_4409_; uint8_t v_suppressInsideQuot_4410_; lean_object* v_savedPos_x3f_4411_; lean_object* v_forbiddenTks_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4426_; 
v_prec_4408_ = lean_ctor_get(v_c_4407_, 0);
v_quotDepth_4409_ = lean_ctor_get(v_c_4407_, 1);
v_suppressInsideQuot_4410_ = lean_ctor_get_uint8(v_c_4407_, sizeof(void*)*4);
v_savedPos_x3f_4411_ = lean_ctor_get(v_c_4407_, 2);
v_forbiddenTks_4412_ = lean_ctor_get(v_c_4407_, 3);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_c_4407_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4414_ = v_c_4407_;
v_isShared_4415_ = v_isSharedCheck_4426_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_forbiddenTks_4412_);
lean_inc(v_savedPos_x3f_4411_);
lean_inc(v_quotDepth_4409_);
lean_inc(v_prec_4408_);
lean_dec(v_c_4407_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4426_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; uint8_t v___x_4418_; 
v___x_4416_ = lean_array_get_size(v_forbiddenTks_4412_);
v___x_4417_ = lean_unsigned_to_nat(0u);
v___x_4418_ = lean_nat_dec_eq(v___x_4416_, v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; lean_object* v___x_4421_; 
v___x_4419_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_forbiddenTks_4412_, v_tks_4406_);
lean_dec_ref(v_tks_4406_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 3, v___x_4419_);
v___x_4421_ = v___x_4414_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_prec_4408_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v_quotDepth_4409_);
lean_ctor_set(v_reuseFailAlloc_4422_, 2, v_savedPos_x3f_4411_);
lean_ctor_set(v_reuseFailAlloc_4422_, 3, v___x_4419_);
lean_ctor_set_uint8(v_reuseFailAlloc_4422_, sizeof(void*)*4, v_suppressInsideQuot_4410_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
else
{
lean_object* v___x_4424_; 
lean_dec_ref(v_forbiddenTks_4412_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 3, v_tks_4406_);
v___x_4424_ = v___x_4414_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_prec_4408_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_quotDepth_4409_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_savedPos_x3f_4411_);
lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_tks_4406_);
lean_ctor_set_uint8(v_reuseFailAlloc_4425_, sizeof(void*)*4, v_suppressInsideQuot_4410_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg(lean_object* v_tks_4427_, lean_object* v_p_4428_){
_start:
{
lean_object* v___f_4429_; lean_object* v___x_4430_; 
v___f_4429_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbiddens___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4429_, 0, v_tks_4427_);
v___x_4430_ = l_Lean_Parser_adaptCacheableContext(v___f_4429_, v_p_4428_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens(lean_object* v_tks_4431_, lean_object* v_p_4432_, lean_object* v___h_4433_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_Parser_withForbiddens___redArg(v_tks_4431_, v_p_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1(){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1));
v___x_4443_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2));
v___x_4444_ = l_Lean_addBuiltinDocString(v___x_4442_, v___x_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___boxed(lean_object* v_a_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4449_){
_start:
{
lean_object* v_prec_4450_; lean_object* v_quotDepth_4451_; uint8_t v_suppressInsideQuot_4452_; lean_object* v_savedPos_x3f_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4461_; 
v_prec_4450_ = lean_ctor_get(v_x_4449_, 0);
v_quotDepth_4451_ = lean_ctor_get(v_x_4449_, 1);
v_suppressInsideQuot_4452_ = lean_ctor_get_uint8(v_x_4449_, sizeof(void*)*4);
v_savedPos_x3f_4453_ = lean_ctor_get(v_x_4449_, 2);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_x_4449_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v_x_4449_, 3);
lean_dec(v_unused_4462_);
v___x_4455_ = v_x_4449_;
v_isShared_4456_ = v_isSharedCheck_4461_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_savedPos_x3f_4453_);
lean_inc(v_quotDepth_4451_);
lean_inc(v_prec_4450_);
lean_dec(v_x_4449_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4461_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4457_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___lam__0___closed__0));
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 3, v___x_4457_);
v___x_4459_ = v___x_4455_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_prec_4450_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_quotDepth_4451_);
lean_ctor_set(v_reuseFailAlloc_4460_, 2, v_savedPos_x3f_4453_);
lean_ctor_set(v_reuseFailAlloc_4460_, 3, v___x_4457_);
lean_ctor_set_uint8(v_reuseFailAlloc_4460_, sizeof(void*)*4, v_suppressInsideQuot_4452_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4464_){
_start:
{
lean_object* v___f_4465_; lean_object* v___x_4466_; 
v___f_4465_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4466_ = l_Lean_Parser_adaptCacheableContext(v___f_4465_, v_p_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4475_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4476_ = l_Lean_addBuiltinDocString(v___x_4474_, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4480_, lean_object* v_s_4481_){
_start:
{
lean_object* v_pos_4482_; lean_object* v_toInputContext_4483_; uint8_t v___x_4484_; 
v_pos_4482_ = lean_ctor_get(v_s_4481_, 2);
v_toInputContext_4483_ = lean_ctor_get(v_c_4480_, 0);
v___x_4484_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4483_, v_pos_4482_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4485_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4486_ = l_Lean_Parser_ParserState_mkError(v_s_4481_, v___x_4485_);
return v___x_4486_;
}
else
{
return v_s_4481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4487_, lean_object* v_s_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_Parser_eoiFn(v_c_4487_, v_s_4488_);
lean_dec_ref(v_c_4487_);
return v_res_4489_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4491_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v___x_4490_);
return v___x_4492_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4494_, lean_object* v_v_4495_, lean_object* v_t_4496_){
_start:
{
if (lean_obj_tag(v_t_4496_) == 0)
{
lean_object* v_size_4497_; lean_object* v_k_4498_; lean_object* v_v_4499_; lean_object* v_l_4500_; lean_object* v_r_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4781_; 
v_size_4497_ = lean_ctor_get(v_t_4496_, 0);
v_k_4498_ = lean_ctor_get(v_t_4496_, 1);
v_v_4499_ = lean_ctor_get(v_t_4496_, 2);
v_l_4500_ = lean_ctor_get(v_t_4496_, 3);
v_r_4501_ = lean_ctor_get(v_t_4496_, 4);
v_isSharedCheck_4781_ = !lean_is_exclusive(v_t_4496_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4503_ = v_t_4496_;
v_isShared_4504_ = v_isSharedCheck_4781_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_r_4501_);
lean_inc(v_l_4500_);
lean_inc(v_v_4499_);
lean_inc(v_k_4498_);
lean_inc(v_size_4497_);
lean_dec(v_t_4496_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4781_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
uint8_t v___x_4505_; 
v___x_4505_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4494_, v_k_4498_);
switch(v___x_4505_)
{
case 0:
{
lean_object* v_impl_4506_; lean_object* v___x_4507_; 
lean_dec(v_size_4497_);
v_impl_4506_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4494_, v_v_4495_, v_l_4500_);
v___x_4507_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4501_) == 0)
{
lean_object* v_size_4508_; lean_object* v_size_4509_; lean_object* v_k_4510_; lean_object* v_v_4511_; lean_object* v_l_4512_; lean_object* v_r_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; 
v_size_4508_ = lean_ctor_get(v_r_4501_, 0);
v_size_4509_ = lean_ctor_get(v_impl_4506_, 0);
v_k_4510_ = lean_ctor_get(v_impl_4506_, 1);
v_v_4511_ = lean_ctor_get(v_impl_4506_, 2);
v_l_4512_ = lean_ctor_get(v_impl_4506_, 3);
v_r_4513_ = lean_ctor_get(v_impl_4506_, 4);
lean_inc(v_r_4513_);
v___x_4514_ = lean_unsigned_to_nat(3u);
v___x_4515_ = lean_nat_mul(v___x_4514_, v_size_4508_);
v___x_4516_ = lean_nat_dec_lt(v___x_4515_, v_size_4509_);
lean_dec(v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
lean_dec(v_r_4513_);
v___x_4517_ = lean_nat_add(v___x_4507_, v_size_4509_);
v___x_4518_ = lean_nat_add(v___x_4517_, v_size_4508_);
lean_dec(v___x_4517_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 3, v_impl_4506_);
lean_ctor_set(v___x_4503_, 0, v___x_4518_);
v___x_4520_ = v___x_4503_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4521_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4521_, 3, v_impl_4506_);
lean_ctor_set(v_reuseFailAlloc_4521_, 4, v_r_4501_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
else
{
lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4587_; 
lean_inc(v_l_4512_);
lean_inc(v_v_4511_);
lean_inc(v_k_4510_);
lean_inc(v_size_4509_);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_impl_4506_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; lean_object* v_unused_4589_; lean_object* v_unused_4590_; lean_object* v_unused_4591_; lean_object* v_unused_4592_; 
v_unused_4588_ = lean_ctor_get(v_impl_4506_, 4);
lean_dec(v_unused_4588_);
v_unused_4589_ = lean_ctor_get(v_impl_4506_, 3);
lean_dec(v_unused_4589_);
v_unused_4590_ = lean_ctor_get(v_impl_4506_, 2);
lean_dec(v_unused_4590_);
v_unused_4591_ = lean_ctor_get(v_impl_4506_, 1);
lean_dec(v_unused_4591_);
v_unused_4592_ = lean_ctor_get(v_impl_4506_, 0);
lean_dec(v_unused_4592_);
v___x_4523_ = v_impl_4506_;
v_isShared_4524_ = v_isSharedCheck_4587_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v_impl_4506_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4587_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_size_4525_; lean_object* v_size_4526_; lean_object* v_k_4527_; lean_object* v_v_4528_; lean_object* v_l_4529_; lean_object* v_r_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v_size_4525_ = lean_ctor_get(v_l_4512_, 0);
v_size_4526_ = lean_ctor_get(v_r_4513_, 0);
v_k_4527_ = lean_ctor_get(v_r_4513_, 1);
v_v_4528_ = lean_ctor_get(v_r_4513_, 2);
v_l_4529_ = lean_ctor_get(v_r_4513_, 3);
v_r_4530_ = lean_ctor_get(v_r_4513_, 4);
v___x_4531_ = lean_unsigned_to_nat(2u);
v___x_4532_ = lean_nat_mul(v___x_4531_, v_size_4525_);
v___x_4533_ = lean_nat_dec_lt(v_size_4526_, v___x_4532_);
lean_dec(v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4562_; 
lean_inc(v_r_4530_);
lean_inc(v_l_4529_);
lean_inc(v_v_4528_);
lean_inc(v_k_4527_);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_r_4513_);
if (v_isSharedCheck_4562_ == 0)
{
lean_object* v_unused_4563_; lean_object* v_unused_4564_; lean_object* v_unused_4565_; lean_object* v_unused_4566_; lean_object* v_unused_4567_; 
v_unused_4563_ = lean_ctor_get(v_r_4513_, 4);
lean_dec(v_unused_4563_);
v_unused_4564_ = lean_ctor_get(v_r_4513_, 3);
lean_dec(v_unused_4564_);
v_unused_4565_ = lean_ctor_get(v_r_4513_, 2);
lean_dec(v_unused_4565_);
v_unused_4566_ = lean_ctor_get(v_r_4513_, 1);
lean_dec(v_unused_4566_);
v_unused_4567_ = lean_ctor_get(v_r_4513_, 0);
lean_dec(v_unused_4567_);
v___x_4535_ = v_r_4513_;
v_isShared_4536_ = v_isSharedCheck_4562_;
goto v_resetjp_4534_;
}
else
{
lean_dec(v_r_4513_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4562_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___x_4550_; lean_object* v___y_4552_; 
v___x_4537_ = lean_nat_add(v___x_4507_, v_size_4509_);
lean_dec(v_size_4509_);
v___x_4538_ = lean_nat_add(v___x_4537_, v_size_4508_);
lean_dec(v___x_4537_);
v___x_4550_ = lean_nat_add(v___x_4507_, v_size_4525_);
if (lean_obj_tag(v_l_4529_) == 0)
{
lean_object* v_size_4560_; 
v_size_4560_ = lean_ctor_get(v_l_4529_, 0);
lean_inc(v_size_4560_);
v___y_4552_ = v_size_4560_;
goto v___jp_4551_;
}
else
{
lean_object* v___x_4561_; 
v___x_4561_ = lean_unsigned_to_nat(0u);
v___y_4552_ = v___x_4561_;
goto v___jp_4551_;
}
v___jp_4539_:
{
lean_object* v___x_4543_; lean_object* v___x_4545_; 
v___x_4543_ = lean_nat_add(v___y_4540_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec(v___y_4540_);
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 4, v_r_4501_);
lean_ctor_set(v___x_4535_, 3, v_r_4530_);
lean_ctor_set(v___x_4535_, 2, v_v_4499_);
lean_ctor_set(v___x_4535_, 1, v_k_4498_);
lean_ctor_set(v___x_4535_, 0, v___x_4543_);
v___x_4545_ = v___x_4535_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4543_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4549_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4549_, 3, v_r_4530_);
lean_ctor_set(v_reuseFailAlloc_4549_, 4, v_r_4501_);
v___x_4545_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4547_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v___x_4545_);
lean_ctor_set(v___x_4523_, 3, v___y_4541_);
lean_ctor_set(v___x_4523_, 2, v_v_4528_);
lean_ctor_set(v___x_4523_, 1, v_k_4527_);
lean_ctor_set(v___x_4523_, 0, v___x_4538_);
v___x_4547_ = v___x_4523_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_k_4527_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_v_4528_);
lean_ctor_set(v_reuseFailAlloc_4548_, 3, v___y_4541_);
lean_ctor_set(v_reuseFailAlloc_4548_, 4, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
v___jp_4551_:
{
lean_object* v___x_4553_; lean_object* v___x_4555_; 
v___x_4553_ = lean_nat_add(v___x_4550_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec(v___x_4550_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v_l_4529_);
lean_ctor_set(v___x_4503_, 3, v_l_4512_);
lean_ctor_set(v___x_4503_, 2, v_v_4511_);
lean_ctor_set(v___x_4503_, 1, v_k_4510_);
lean_ctor_set(v___x_4503_, 0, v___x_4553_);
v___x_4555_ = v___x_4503_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v_k_4510_);
lean_ctor_set(v_reuseFailAlloc_4559_, 2, v_v_4511_);
lean_ctor_set(v_reuseFailAlloc_4559_, 3, v_l_4512_);
lean_ctor_set(v_reuseFailAlloc_4559_, 4, v_l_4529_);
v___x_4555_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4556_; 
v___x_4556_ = lean_nat_add(v___x_4507_, v_size_4508_);
if (lean_obj_tag(v_r_4530_) == 0)
{
lean_object* v_size_4557_; 
v_size_4557_ = lean_ctor_get(v_r_4530_, 0);
lean_inc(v_size_4557_);
v___y_4540_ = v___x_4556_;
v___y_4541_ = v___x_4555_;
v___y_4542_ = v_size_4557_;
goto v___jp_4539_;
}
else
{
lean_object* v___x_4558_; 
v___x_4558_ = lean_unsigned_to_nat(0u);
v___y_4540_ = v___x_4556_;
v___y_4541_ = v___x_4555_;
v___y_4542_ = v___x_4558_;
goto v___jp_4539_;
}
}
}
}
}
else
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4573_; 
lean_del_object(v___x_4503_);
v___x_4568_ = lean_nat_add(v___x_4507_, v_size_4509_);
lean_dec(v_size_4509_);
v___x_4569_ = lean_nat_add(v___x_4568_, v_size_4508_);
lean_dec(v___x_4568_);
v___x_4570_ = lean_nat_add(v___x_4507_, v_size_4508_);
v___x_4571_ = lean_nat_add(v___x_4570_, v_size_4526_);
lean_dec(v___x_4570_);
lean_inc_ref(v_r_4501_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_r_4501_);
lean_ctor_set(v___x_4523_, 3, v_r_4513_);
lean_ctor_set(v___x_4523_, 2, v_v_4499_);
lean_ctor_set(v___x_4523_, 1, v_k_4498_);
lean_ctor_set(v___x_4523_, 0, v___x_4571_);
v___x_4573_ = v___x_4523_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4586_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4586_, 3, v_r_4513_);
lean_ctor_set(v_reuseFailAlloc_4586_, 4, v_r_4501_);
v___x_4573_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
v_isSharedCheck_4580_ = !lean_is_exclusive(v_r_4501_);
if (v_isSharedCheck_4580_ == 0)
{
lean_object* v_unused_4581_; lean_object* v_unused_4582_; lean_object* v_unused_4583_; lean_object* v_unused_4584_; lean_object* v_unused_4585_; 
v_unused_4581_ = lean_ctor_get(v_r_4501_, 4);
lean_dec(v_unused_4581_);
v_unused_4582_ = lean_ctor_get(v_r_4501_, 3);
lean_dec(v_unused_4582_);
v_unused_4583_ = lean_ctor_get(v_r_4501_, 2);
lean_dec(v_unused_4583_);
v_unused_4584_ = lean_ctor_get(v_r_4501_, 1);
lean_dec(v_unused_4584_);
v_unused_4585_ = lean_ctor_get(v_r_4501_, 0);
lean_dec(v_unused_4585_);
v___x_4575_ = v_r_4501_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_dec(v_r_4501_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 4, v___x_4573_);
lean_ctor_set(v___x_4575_, 3, v_l_4512_);
lean_ctor_set(v___x_4575_, 2, v_v_4511_);
lean_ctor_set(v___x_4575_, 1, v_k_4510_);
lean_ctor_set(v___x_4575_, 0, v___x_4569_);
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4569_);
lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_k_4510_);
lean_ctor_set(v_reuseFailAlloc_4579_, 2, v_v_4511_);
lean_ctor_set(v_reuseFailAlloc_4579_, 3, v_l_4512_);
lean_ctor_set(v_reuseFailAlloc_4579_, 4, v___x_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4593_; 
v_l_4593_ = lean_ctor_get(v_impl_4506_, 3);
if (lean_obj_tag(v_l_4593_) == 0)
{
lean_object* v_r_4594_; lean_object* v_k_4595_; lean_object* v_v_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4607_; 
lean_inc_ref(v_l_4593_);
v_r_4594_ = lean_ctor_get(v_impl_4506_, 4);
v_k_4595_ = lean_ctor_get(v_impl_4506_, 1);
v_v_4596_ = lean_ctor_get(v_impl_4506_, 2);
v_isSharedCheck_4607_ = !lean_is_exclusive(v_impl_4506_);
if (v_isSharedCheck_4607_ == 0)
{
lean_object* v_unused_4608_; lean_object* v_unused_4609_; 
v_unused_4608_ = lean_ctor_get(v_impl_4506_, 3);
lean_dec(v_unused_4608_);
v_unused_4609_ = lean_ctor_get(v_impl_4506_, 0);
lean_dec(v_unused_4609_);
v___x_4598_ = v_impl_4506_;
v_isShared_4599_ = v_isSharedCheck_4607_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_r_4594_);
lean_inc(v_v_4596_);
lean_inc(v_k_4595_);
lean_dec(v_impl_4506_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4607_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4594_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 3, v_r_4594_);
lean_ctor_set(v___x_4598_, 2, v_v_4499_);
lean_ctor_set(v___x_4598_, 1, v_k_4498_);
lean_ctor_set(v___x_4598_, 0, v___x_4507_);
v___x_4602_ = v___x_4598_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v_r_4594_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v_r_4594_);
v___x_4602_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4604_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v___x_4602_);
lean_ctor_set(v___x_4503_, 3, v_l_4593_);
lean_ctor_set(v___x_4503_, 2, v_v_4596_);
lean_ctor_set(v___x_4503_, 1, v_k_4595_);
lean_ctor_set(v___x_4503_, 0, v___x_4600_);
v___x_4604_ = v___x_4503_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_k_4595_);
lean_ctor_set(v_reuseFailAlloc_4605_, 2, v_v_4596_);
lean_ctor_set(v_reuseFailAlloc_4605_, 3, v_l_4593_);
lean_ctor_set(v_reuseFailAlloc_4605_, 4, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
lean_object* v_r_4610_; 
v_r_4610_ = lean_ctor_get(v_impl_4506_, 4);
lean_inc(v_r_4610_);
if (lean_obj_tag(v_r_4610_) == 0)
{
lean_object* v_k_4611_; lean_object* v_v_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4635_; 
lean_inc(v_l_4593_);
v_k_4611_ = lean_ctor_get(v_impl_4506_, 1);
v_v_4612_ = lean_ctor_get(v_impl_4506_, 2);
v_isSharedCheck_4635_ = !lean_is_exclusive(v_impl_4506_);
if (v_isSharedCheck_4635_ == 0)
{
lean_object* v_unused_4636_; lean_object* v_unused_4637_; lean_object* v_unused_4638_; 
v_unused_4636_ = lean_ctor_get(v_impl_4506_, 4);
lean_dec(v_unused_4636_);
v_unused_4637_ = lean_ctor_get(v_impl_4506_, 3);
lean_dec(v_unused_4637_);
v_unused_4638_ = lean_ctor_get(v_impl_4506_, 0);
lean_dec(v_unused_4638_);
v___x_4614_ = v_impl_4506_;
v_isShared_4615_ = v_isSharedCheck_4635_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_v_4612_);
lean_inc(v_k_4611_);
lean_dec(v_impl_4506_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4635_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_k_4616_; lean_object* v_v_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4631_; 
v_k_4616_ = lean_ctor_get(v_r_4610_, 1);
v_v_4617_ = lean_ctor_get(v_r_4610_, 2);
v_isSharedCheck_4631_ = !lean_is_exclusive(v_r_4610_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; lean_object* v_unused_4633_; lean_object* v_unused_4634_; 
v_unused_4632_ = lean_ctor_get(v_r_4610_, 4);
lean_dec(v_unused_4632_);
v_unused_4633_ = lean_ctor_get(v_r_4610_, 3);
lean_dec(v_unused_4633_);
v_unused_4634_ = lean_ctor_get(v_r_4610_, 0);
lean_dec(v_unused_4634_);
v___x_4619_ = v_r_4610_;
v_isShared_4620_ = v_isSharedCheck_4631_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_v_4617_);
lean_inc(v_k_4616_);
lean_dec(v_r_4610_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4631_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4621_ = lean_unsigned_to_nat(3u);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 4, v_l_4593_);
lean_ctor_set(v___x_4619_, 3, v_l_4593_);
lean_ctor_set(v___x_4619_, 2, v_v_4612_);
lean_ctor_set(v___x_4619_, 1, v_k_4611_);
lean_ctor_set(v___x_4619_, 0, v___x_4507_);
v___x_4623_ = v___x_4619_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_k_4611_);
lean_ctor_set(v_reuseFailAlloc_4630_, 2, v_v_4612_);
lean_ctor_set(v_reuseFailAlloc_4630_, 3, v_l_4593_);
lean_ctor_set(v_reuseFailAlloc_4630_, 4, v_l_4593_);
v___x_4623_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4625_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 4, v_l_4593_);
lean_ctor_set(v___x_4614_, 2, v_v_4499_);
lean_ctor_set(v___x_4614_, 1, v_k_4498_);
lean_ctor_set(v___x_4614_, 0, v___x_4507_);
v___x_4625_ = v___x_4614_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4629_, 3, v_l_4593_);
lean_ctor_set(v_reuseFailAlloc_4629_, 4, v_l_4593_);
v___x_4625_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4627_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v___x_4625_);
lean_ctor_set(v___x_4503_, 3, v___x_4623_);
lean_ctor_set(v___x_4503_, 2, v_v_4617_);
lean_ctor_set(v___x_4503_, 1, v_k_4616_);
lean_ctor_set(v___x_4503_, 0, v___x_4621_);
v___x_4627_ = v___x_4503_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_k_4616_);
lean_ctor_set(v_reuseFailAlloc_4628_, 2, v_v_4617_);
lean_ctor_set(v_reuseFailAlloc_4628_, 3, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4628_, 4, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4639_ = lean_unsigned_to_nat(2u);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v_r_4610_);
lean_ctor_set(v___x_4503_, 3, v_impl_4506_);
lean_ctor_set(v___x_4503_, 0, v___x_4639_);
v___x_4641_ = v___x_4503_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4642_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4642_, 3, v_impl_4506_);
lean_ctor_set(v_reuseFailAlloc_4642_, 4, v_r_4610_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4644_; 
lean_dec(v_v_4499_);
lean_dec(v_k_4498_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 2, v_v_4495_);
lean_ctor_set(v___x_4503_, 1, v_k_4494_);
v___x_4644_ = v___x_4503_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_size_4497_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v_k_4494_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_v_4495_);
lean_ctor_set(v_reuseFailAlloc_4645_, 3, v_l_4500_);
lean_ctor_set(v_reuseFailAlloc_4645_, 4, v_r_4501_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
default: 
{
lean_object* v_impl_4646_; lean_object* v___x_4647_; 
lean_dec(v_size_4497_);
v_impl_4646_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4494_, v_v_4495_, v_r_4501_);
v___x_4647_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4500_) == 0)
{
lean_object* v_size_4648_; lean_object* v_size_4649_; lean_object* v_k_4650_; lean_object* v_v_4651_; lean_object* v_l_4652_; lean_object* v_r_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; 
v_size_4648_ = lean_ctor_get(v_l_4500_, 0);
v_size_4649_ = lean_ctor_get(v_impl_4646_, 0);
v_k_4650_ = lean_ctor_get(v_impl_4646_, 1);
v_v_4651_ = lean_ctor_get(v_impl_4646_, 2);
v_l_4652_ = lean_ctor_get(v_impl_4646_, 3);
lean_inc(v_l_4652_);
v_r_4653_ = lean_ctor_get(v_impl_4646_, 4);
v___x_4654_ = lean_unsigned_to_nat(3u);
v___x_4655_ = lean_nat_mul(v___x_4654_, v_size_4648_);
v___x_4656_ = lean_nat_dec_lt(v___x_4655_, v_size_4649_);
lean_dec(v___x_4655_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4660_; 
lean_dec(v_l_4652_);
v___x_4657_ = lean_nat_add(v___x_4647_, v_size_4648_);
v___x_4658_ = lean_nat_add(v___x_4657_, v_size_4649_);
lean_dec(v___x_4657_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v_impl_4646_);
lean_ctor_set(v___x_4503_, 0, v___x_4658_);
v___x_4660_ = v___x_4503_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4661_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4661_, 3, v_l_4500_);
lean_ctor_set(v_reuseFailAlloc_4661_, 4, v_impl_4646_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
else
{
lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4725_; 
lean_inc(v_r_4653_);
lean_inc(v_v_4651_);
lean_inc(v_k_4650_);
lean_inc(v_size_4649_);
v_isSharedCheck_4725_ = !lean_is_exclusive(v_impl_4646_);
if (v_isSharedCheck_4725_ == 0)
{
lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; lean_object* v_unused_4730_; 
v_unused_4726_ = lean_ctor_get(v_impl_4646_, 4);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_impl_4646_, 3);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_impl_4646_, 2);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_impl_4646_, 1);
lean_dec(v_unused_4729_);
v_unused_4730_ = lean_ctor_get(v_impl_4646_, 0);
lean_dec(v_unused_4730_);
v___x_4663_ = v_impl_4646_;
v_isShared_4664_ = v_isSharedCheck_4725_;
goto v_resetjp_4662_;
}
else
{
lean_dec(v_impl_4646_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4725_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v_size_4665_; lean_object* v_k_4666_; lean_object* v_v_4667_; lean_object* v_l_4668_; lean_object* v_r_4669_; lean_object* v_size_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v_size_4665_ = lean_ctor_get(v_l_4652_, 0);
v_k_4666_ = lean_ctor_get(v_l_4652_, 1);
v_v_4667_ = lean_ctor_get(v_l_4652_, 2);
v_l_4668_ = lean_ctor_get(v_l_4652_, 3);
v_r_4669_ = lean_ctor_get(v_l_4652_, 4);
v_size_4670_ = lean_ctor_get(v_r_4653_, 0);
v___x_4671_ = lean_unsigned_to_nat(2u);
v___x_4672_ = lean_nat_mul(v___x_4671_, v_size_4670_);
v___x_4673_ = lean_nat_dec_lt(v_size_4665_, v___x_4672_);
lean_dec(v___x_4672_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4701_; 
lean_inc(v_r_4669_);
lean_inc(v_l_4668_);
lean_inc(v_v_4667_);
lean_inc(v_k_4666_);
v_isSharedCheck_4701_ = !lean_is_exclusive(v_l_4652_);
if (v_isSharedCheck_4701_ == 0)
{
lean_object* v_unused_4702_; lean_object* v_unused_4703_; lean_object* v_unused_4704_; lean_object* v_unused_4705_; lean_object* v_unused_4706_; 
v_unused_4702_ = lean_ctor_get(v_l_4652_, 4);
lean_dec(v_unused_4702_);
v_unused_4703_ = lean_ctor_get(v_l_4652_, 3);
lean_dec(v_unused_4703_);
v_unused_4704_ = lean_ctor_get(v_l_4652_, 2);
lean_dec(v_unused_4704_);
v_unused_4705_ = lean_ctor_get(v_l_4652_, 1);
lean_dec(v_unused_4705_);
v_unused_4706_ = lean_ctor_get(v_l_4652_, 0);
lean_dec(v_unused_4706_);
v___x_4675_ = v_l_4652_;
v_isShared_4676_ = v_isSharedCheck_4701_;
goto v_resetjp_4674_;
}
else
{
lean_dec(v_l_4652_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4701_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4691_; 
v___x_4677_ = lean_nat_add(v___x_4647_, v_size_4648_);
v___x_4678_ = lean_nat_add(v___x_4677_, v_size_4649_);
lean_dec(v_size_4649_);
if (lean_obj_tag(v_l_4668_) == 0)
{
lean_object* v_size_4699_; 
v_size_4699_ = lean_ctor_get(v_l_4668_, 0);
lean_inc(v_size_4699_);
v___y_4691_ = v_size_4699_;
goto v___jp_4690_;
}
else
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_unsigned_to_nat(0u);
v___y_4691_ = v___x_4700_;
goto v___jp_4690_;
}
v___jp_4679_:
{
lean_object* v___x_4683_; lean_object* v___x_4685_; 
v___x_4683_ = lean_nat_add(v___y_4680_, v___y_4682_);
lean_dec(v___y_4682_);
lean_dec(v___y_4680_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 4, v_r_4653_);
lean_ctor_set(v___x_4675_, 3, v_r_4669_);
lean_ctor_set(v___x_4675_, 2, v_v_4651_);
lean_ctor_set(v___x_4675_, 1, v_k_4650_);
lean_ctor_set(v___x_4675_, 0, v___x_4683_);
v___x_4685_ = v___x_4675_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4683_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_k_4650_);
lean_ctor_set(v_reuseFailAlloc_4689_, 2, v_v_4651_);
lean_ctor_set(v_reuseFailAlloc_4689_, 3, v_r_4669_);
lean_ctor_set(v_reuseFailAlloc_4689_, 4, v_r_4653_);
v___x_4685_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4687_; 
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 4, v___x_4685_);
lean_ctor_set(v___x_4663_, 3, v___y_4681_);
lean_ctor_set(v___x_4663_, 2, v_v_4667_);
lean_ctor_set(v___x_4663_, 1, v_k_4666_);
lean_ctor_set(v___x_4663_, 0, v___x_4678_);
v___x_4687_ = v___x_4663_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v_k_4666_);
lean_ctor_set(v_reuseFailAlloc_4688_, 2, v_v_4667_);
lean_ctor_set(v_reuseFailAlloc_4688_, 3, v___y_4681_);
lean_ctor_set(v_reuseFailAlloc_4688_, 4, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
v___jp_4690_:
{
lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4692_ = lean_nat_add(v___x_4677_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec(v___x_4677_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v_l_4668_);
lean_ctor_set(v___x_4503_, 0, v___x_4692_);
v___x_4694_ = v___x_4503_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4692_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4698_, 3, v_l_4500_);
lean_ctor_set(v_reuseFailAlloc_4698_, 4, v_l_4668_);
v___x_4694_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
lean_object* v___x_4695_; 
v___x_4695_ = lean_nat_add(v___x_4647_, v_size_4670_);
if (lean_obj_tag(v_r_4669_) == 0)
{
lean_object* v_size_4696_; 
v_size_4696_ = lean_ctor_get(v_r_4669_, 0);
lean_inc(v_size_4696_);
v___y_4680_ = v___x_4695_;
v___y_4681_ = v___x_4694_;
v___y_4682_ = v_size_4696_;
goto v___jp_4679_;
}
else
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_unsigned_to_nat(0u);
v___y_4680_ = v___x_4695_;
v___y_4681_ = v___x_4694_;
v___y_4682_ = v___x_4697_;
goto v___jp_4679_;
}
}
}
}
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
lean_del_object(v___x_4503_);
v___x_4707_ = lean_nat_add(v___x_4647_, v_size_4648_);
v___x_4708_ = lean_nat_add(v___x_4707_, v_size_4649_);
lean_dec(v_size_4649_);
v___x_4709_ = lean_nat_add(v___x_4707_, v_size_4665_);
lean_dec(v___x_4707_);
lean_inc_ref(v_l_4500_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 4, v_l_4652_);
lean_ctor_set(v___x_4663_, 3, v_l_4500_);
lean_ctor_set(v___x_4663_, 2, v_v_4499_);
lean_ctor_set(v___x_4663_, 1, v_k_4498_);
lean_ctor_set(v___x_4663_, 0, v___x_4709_);
v___x_4711_ = v___x_4663_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4724_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4724_, 3, v_l_4500_);
lean_ctor_set(v_reuseFailAlloc_4724_, 4, v_l_4652_);
v___x_4711_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
v_isSharedCheck_4718_ = !lean_is_exclusive(v_l_4500_);
if (v_isSharedCheck_4718_ == 0)
{
lean_object* v_unused_4719_; lean_object* v_unused_4720_; lean_object* v_unused_4721_; lean_object* v_unused_4722_; lean_object* v_unused_4723_; 
v_unused_4719_ = lean_ctor_get(v_l_4500_, 4);
lean_dec(v_unused_4719_);
v_unused_4720_ = lean_ctor_get(v_l_4500_, 3);
lean_dec(v_unused_4720_);
v_unused_4721_ = lean_ctor_get(v_l_4500_, 2);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_l_4500_, 1);
lean_dec(v_unused_4722_);
v_unused_4723_ = lean_ctor_get(v_l_4500_, 0);
lean_dec(v_unused_4723_);
v___x_4713_ = v_l_4500_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_dec(v_l_4500_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 4, v_r_4653_);
lean_ctor_set(v___x_4713_, 3, v___x_4711_);
lean_ctor_set(v___x_4713_, 2, v_v_4651_);
lean_ctor_set(v___x_4713_, 1, v_k_4650_);
lean_ctor_set(v___x_4713_, 0, v___x_4708_);
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4708_);
lean_ctor_set(v_reuseFailAlloc_4717_, 1, v_k_4650_);
lean_ctor_set(v_reuseFailAlloc_4717_, 2, v_v_4651_);
lean_ctor_set(v_reuseFailAlloc_4717_, 3, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4717_, 4, v_r_4653_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4731_; 
v_l_4731_ = lean_ctor_get(v_impl_4646_, 3);
lean_inc(v_l_4731_);
if (lean_obj_tag(v_l_4731_) == 0)
{
lean_object* v_r_4732_; lean_object* v_k_4733_; lean_object* v_v_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4757_; 
v_r_4732_ = lean_ctor_get(v_impl_4646_, 4);
v_k_4733_ = lean_ctor_get(v_impl_4646_, 1);
v_v_4734_ = lean_ctor_get(v_impl_4646_, 2);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_impl_4646_);
if (v_isSharedCheck_4757_ == 0)
{
lean_object* v_unused_4758_; lean_object* v_unused_4759_; 
v_unused_4758_ = lean_ctor_get(v_impl_4646_, 3);
lean_dec(v_unused_4758_);
v_unused_4759_ = lean_ctor_get(v_impl_4646_, 0);
lean_dec(v_unused_4759_);
v___x_4736_ = v_impl_4646_;
v_isShared_4737_ = v_isSharedCheck_4757_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_r_4732_);
lean_inc(v_v_4734_);
lean_inc(v_k_4733_);
lean_dec(v_impl_4646_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4757_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v_k_4738_; lean_object* v_v_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4753_; 
v_k_4738_ = lean_ctor_get(v_l_4731_, 1);
v_v_4739_ = lean_ctor_get(v_l_4731_, 2);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_l_4731_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; lean_object* v_unused_4755_; lean_object* v_unused_4756_; 
v_unused_4754_ = lean_ctor_get(v_l_4731_, 4);
lean_dec(v_unused_4754_);
v_unused_4755_ = lean_ctor_get(v_l_4731_, 3);
lean_dec(v_unused_4755_);
v_unused_4756_ = lean_ctor_get(v_l_4731_, 0);
lean_dec(v_unused_4756_);
v___x_4741_ = v_l_4731_;
v_isShared_4742_ = v_isSharedCheck_4753_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_v_4739_);
lean_inc(v_k_4738_);
lean_dec(v_l_4731_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4753_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4743_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4732_, 2);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 4, v_r_4732_);
lean_ctor_set(v___x_4741_, 3, v_r_4732_);
lean_ctor_set(v___x_4741_, 2, v_v_4499_);
lean_ctor_set(v___x_4741_, 1, v_k_4498_);
lean_ctor_set(v___x_4741_, 0, v___x_4647_);
v___x_4745_ = v___x_4741_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4752_, 3, v_r_4732_);
lean_ctor_set(v_reuseFailAlloc_4752_, 4, v_r_4732_);
v___x_4745_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4747_; 
lean_inc(v_r_4732_);
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 3, v_r_4732_);
lean_ctor_set(v___x_4736_, 0, v___x_4647_);
v___x_4747_ = v___x_4736_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v_k_4733_);
lean_ctor_set(v_reuseFailAlloc_4751_, 2, v_v_4734_);
lean_ctor_set(v_reuseFailAlloc_4751_, 3, v_r_4732_);
lean_ctor_set(v_reuseFailAlloc_4751_, 4, v_r_4732_);
v___x_4747_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v___x_4747_);
lean_ctor_set(v___x_4503_, 3, v___x_4745_);
lean_ctor_set(v___x_4503_, 2, v_v_4739_);
lean_ctor_set(v___x_4503_, 1, v_k_4738_);
lean_ctor_set(v___x_4503_, 0, v___x_4743_);
v___x_4749_ = v___x_4503_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_k_4738_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_v_4739_);
lean_ctor_set(v_reuseFailAlloc_4750_, 3, v___x_4745_);
lean_ctor_set(v_reuseFailAlloc_4750_, 4, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
else
{
lean_object* v_r_4760_; 
v_r_4760_ = lean_ctor_get(v_impl_4646_, 4);
lean_inc(v_r_4760_);
if (lean_obj_tag(v_r_4760_) == 0)
{
lean_object* v_k_4761_; lean_object* v_v_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4773_; 
v_k_4761_ = lean_ctor_get(v_impl_4646_, 1);
v_v_4762_ = lean_ctor_get(v_impl_4646_, 2);
v_isSharedCheck_4773_ = !lean_is_exclusive(v_impl_4646_);
if (v_isSharedCheck_4773_ == 0)
{
lean_object* v_unused_4774_; lean_object* v_unused_4775_; lean_object* v_unused_4776_; 
v_unused_4774_ = lean_ctor_get(v_impl_4646_, 4);
lean_dec(v_unused_4774_);
v_unused_4775_ = lean_ctor_get(v_impl_4646_, 3);
lean_dec(v_unused_4775_);
v_unused_4776_ = lean_ctor_get(v_impl_4646_, 0);
lean_dec(v_unused_4776_);
v___x_4764_ = v_impl_4646_;
v_isShared_4765_ = v_isSharedCheck_4773_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_v_4762_);
lean_inc(v_k_4761_);
lean_dec(v_impl_4646_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4773_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4766_ = lean_unsigned_to_nat(3u);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 4, v_l_4731_);
lean_ctor_set(v___x_4764_, 2, v_v_4499_);
lean_ctor_set(v___x_4764_, 1, v_k_4498_);
lean_ctor_set(v___x_4764_, 0, v___x_4647_);
v___x_4768_ = v___x_4764_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4772_, 3, v_l_4731_);
lean_ctor_set(v_reuseFailAlloc_4772_, 4, v_l_4731_);
v___x_4768_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4770_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v_r_4760_);
lean_ctor_set(v___x_4503_, 3, v___x_4768_);
lean_ctor_set(v___x_4503_, 2, v_v_4762_);
lean_ctor_set(v___x_4503_, 1, v_k_4761_);
lean_ctor_set(v___x_4503_, 0, v___x_4766_);
v___x_4770_ = v___x_4503_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_k_4761_);
lean_ctor_set(v_reuseFailAlloc_4771_, 2, v_v_4762_);
lean_ctor_set(v_reuseFailAlloc_4771_, 3, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4771_, 4, v_r_4760_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4777_ = lean_unsigned_to_nat(2u);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v_impl_4646_);
lean_ctor_set(v___x_4503_, 3, v_r_4760_);
lean_ctor_set(v___x_4503_, 0, v___x_4777_);
v___x_4779_ = v___x_4503_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_k_4498_);
lean_ctor_set(v_reuseFailAlloc_4780_, 2, v_v_4499_);
lean_ctor_set(v_reuseFailAlloc_4780_, 3, v_r_4760_);
lean_ctor_set(v_reuseFailAlloc_4780_, 4, v_impl_4646_);
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
}
}
else
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_unsigned_to_nat(1u);
v___x_4783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
lean_ctor_set(v___x_4783_, 1, v_k_4494_);
lean_ctor_set(v___x_4783_, 2, v_v_4495_);
lean_ctor_set(v___x_4783_, 3, v_t_4496_);
lean_ctor_set(v___x_4783_, 4, v_t_4496_);
return v___x_4783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4784_, lean_object* v_k_4785_){
_start:
{
if (lean_obj_tag(v_t_4784_) == 0)
{
lean_object* v_k_4786_; lean_object* v_v_4787_; lean_object* v_l_4788_; lean_object* v_r_4789_; uint8_t v___x_4790_; 
v_k_4786_ = lean_ctor_get(v_t_4784_, 1);
v_v_4787_ = lean_ctor_get(v_t_4784_, 2);
v_l_4788_ = lean_ctor_get(v_t_4784_, 3);
v_r_4789_ = lean_ctor_get(v_t_4784_, 4);
v___x_4790_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4785_, v_k_4786_);
switch(v___x_4790_)
{
case 0:
{
v_t_4784_ = v_l_4788_;
goto _start;
}
case 1:
{
lean_object* v___x_4792_; 
lean_inc(v_v_4787_);
v___x_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4792_, 0, v_v_4787_);
return v___x_4792_;
}
default: 
{
v_t_4784_ = v_r_4789_;
goto _start;
}
}
}
else
{
lean_object* v___x_4794_; 
v___x_4794_ = lean_box(0);
return v___x_4794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4795_, lean_object* v_k_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4795_, v_k_4796_);
lean_dec(v_k_4796_);
lean_dec(v_t_4795_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4798_, lean_object* v_k_4799_, lean_object* v_v_4800_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4798_, v_k_4799_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = lean_box(0);
v___x_4803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4803_, 0, v_v_4800_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
v___x_4804_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4799_, v___x_4803_, v_map_4798_);
return v___x_4804_;
}
else
{
lean_object* v_val_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v_val_4805_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_val_4805_);
lean_dec_ref_known(v___x_4801_, 1);
v___x_4806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4806_, 0, v_v_4800_);
lean_ctor_set(v___x_4806_, 1, v_val_4805_);
v___x_4807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4799_, v___x_4806_, v_map_4798_);
return v___x_4807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4808_, lean_object* v_map_4809_, lean_object* v_k_4810_, lean_object* v_v_4811_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4809_, v_k_4810_, v_v_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4813_, lean_object* v_t_4814_, lean_object* v_k_4815_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4814_, v_k_4815_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4817_, lean_object* v_t_4818_, lean_object* v_k_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4817_, v_t_4818_, v_k_4819_);
lean_dec(v_k_4819_);
lean_dec(v_t_4818_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4821_, lean_object* v_k_4822_, lean_object* v_v_4823_, lean_object* v_t_4824_, lean_object* v_hl_4825_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4822_, v_v_4823_, v_t_4824_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_box(1);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg___boxed(lean_object* v___dummy_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_Parser_TokenMap_instInhabited___redArg();
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4831_){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_box(1);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_box(1);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_Parser_TokenMap_instEmptyCollection___redArg();
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4837_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = lean_box(1);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4839_, lean_object* v_a_4840_, lean_object* v_b_4841_, lean_object* v_c_4842_){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4843_, 0, v_a_4840_);
lean_ctor_set(v___x_4843_, 1, v_b_4841_);
v___x_4844_ = lean_apply_2(v_f_4839_, v___x_4843_, v_c_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4845_, lean_object* v_____do__lift_4846_){
_start:
{
lean_object* v_a_4847_; lean_object* v___x_4848_; 
v_a_4847_ = lean_ctor_get(v_____do__lift_4846_, 0);
lean_inc(v_a_4847_);
lean_dec_ref(v_____do__lift_4846_);
v___x_4848_ = lean_apply_2(v_toPure_4845_, lean_box(0), v_a_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4849_, lean_object* v_m_4850_, lean_object* v_init_4851_, lean_object* v_f_4852_){
_start:
{
lean_object* v_toApplicative_4853_; lean_object* v_toBind_4854_; lean_object* v_toPure_4855_; lean_object* v___f_4856_; lean_object* v___x_4857_; lean_object* v___f_4858_; lean_object* v___x_4859_; 
v_toApplicative_4853_ = lean_ctor_get(v_inst_4849_, 0);
v_toBind_4854_ = lean_ctor_get(v_inst_4849_, 1);
lean_inc(v_toBind_4854_);
v_toPure_4855_ = lean_ctor_get(v_toApplicative_4853_, 1);
lean_inc(v_toPure_4855_);
v___f_4856_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4856_, 0, v_f_4852_);
v___x_4857_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4849_, v___f_4856_, v_init_4851_, v_m_4850_);
v___f_4858_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4858_, 0, v_toPure_4855_);
v___x_4859_ = lean_apply_4(v_toBind_4854_, lean_box(0), lean_box(0), v___x_4857_, v___f_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4860_, lean_object* v_00_u03b1_4861_, lean_object* v_inst_4862_, lean_object* v_00_u03b2_4863_, lean_object* v_m_4864_, lean_object* v_init_4865_, lean_object* v_f_4866_){
_start:
{
lean_object* v_toApplicative_4867_; lean_object* v_toBind_4868_; lean_object* v_toPure_4869_; lean_object* v___f_4870_; lean_object* v___x_4871_; lean_object* v___f_4872_; lean_object* v___x_4873_; 
v_toApplicative_4867_ = lean_ctor_get(v_inst_4862_, 0);
v_toBind_4868_ = lean_ctor_get(v_inst_4862_, 1);
lean_inc(v_toBind_4868_);
v_toPure_4869_ = lean_ctor_get(v_toApplicative_4867_, 1);
lean_inc(v_toPure_4869_);
v___f_4870_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4870_, 0, v_f_4866_);
v___x_4871_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4862_, v___f_4870_, v_init_4865_, v_m_4864_);
v___f_4872_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4872_, 0, v_toPure_4869_);
v___x_4873_ = lean_apply_4(v_toBind_4868_, lean_box(0), lean_box(0), v___x_4871_, v___f_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4874_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4875_, 0, lean_box(0));
lean_closure_set(v___x_4875_, 1, lean_box(0));
lean_closure_set(v___x_4875_, 2, v_inst_4874_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4876_, lean_object* v_00_u03b1_4877_, lean_object* v_inst_4878_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4879_, 0, lean_box(0));
lean_closure_set(v___x_4879_, 1, lean_box(0));
lean_closure_set(v___x_4879_, 2, v_inst_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(uint8_t v_x_4884_){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = lean_box(v_x_4884_);
v___x_4886_ = lean_obj_tag_nat(v___x_4885_);
lean_dec(v___x_4885_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl___boxed(lean_object* v_x_4887_){
_start:
{
uint8_t v_x_4__boxed_4888_; lean_object* v_res_4889_; 
v_x_4__boxed_4888_ = lean_unbox(v_x_4887_);
v_res_4889_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(v_x_4__boxed_4888_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4890_){
_start:
{
lean_inc(v_k_4890_);
return v_k_4890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4891_);
lean_dec(v_k_4891_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4893_, lean_object* v_ctorIdx_4894_, uint8_t v_t_4895_, lean_object* v_h_4896_, lean_object* v_k_4897_){
_start:
{
lean_inc(v_k_4897_);
return v_k_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4898_, lean_object* v_ctorIdx_4899_, lean_object* v_t_4900_, lean_object* v_h_4901_, lean_object* v_k_4902_){
_start:
{
uint8_t v_t_boxed_4903_; lean_object* v_res_4904_; 
v_t_boxed_4903_ = lean_unbox(v_t_4900_);
v_res_4904_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4898_, v_ctorIdx_4899_, v_t_boxed_4903_, v_h_4901_, v_k_4902_);
lean_dec(v_k_4902_);
lean_dec(v_ctorIdx_4899_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4905_){
_start:
{
lean_inc(v_default_4905_);
return v_default_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4906_);
lean_dec(v_default_4906_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4908_, uint8_t v_t_4909_, lean_object* v_h_4910_, lean_object* v_default_4911_){
_start:
{
lean_inc(v_default_4911_);
return v_default_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4912_, lean_object* v_t_4913_, lean_object* v_h_4914_, lean_object* v_default_4915_){
_start:
{
uint8_t v_t_boxed_4916_; lean_object* v_res_4917_; 
v_t_boxed_4916_ = lean_unbox(v_t_4913_);
v_res_4917_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4912_, v_t_boxed_4916_, v_h_4914_, v_default_4915_);
lean_dec(v_default_4915_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4918_){
_start:
{
lean_inc(v_symbol_4918_);
return v_symbol_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4919_);
lean_dec(v_symbol_4919_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4921_, uint8_t v_t_4922_, lean_object* v_h_4923_, lean_object* v_symbol_4924_){
_start:
{
lean_inc(v_symbol_4924_);
return v_symbol_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4925_, lean_object* v_t_4926_, lean_object* v_h_4927_, lean_object* v_symbol_4928_){
_start:
{
uint8_t v_t_boxed_4929_; lean_object* v_res_4930_; 
v_t_boxed_4929_ = lean_unbox(v_t_4926_);
v_res_4930_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4925_, v_t_boxed_4929_, v_h_4927_, v_symbol_4928_);
lean_dec(v_symbol_4928_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4931_){
_start:
{
lean_inc(v_both_4931_);
return v_both_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4932_);
lean_dec(v_both_4932_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4934_, uint8_t v_t_4935_, lean_object* v_h_4936_, lean_object* v_both_4937_){
_start:
{
lean_inc(v_both_4937_);
return v_both_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4938_, lean_object* v_t_4939_, lean_object* v_h_4940_, lean_object* v_both_4941_){
_start:
{
uint8_t v_t_boxed_4942_; lean_object* v_res_4943_; 
v_t_boxed_4942_ = lean_unbox(v_t_4939_);
v_res_4943_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4938_, v_t_boxed_4942_, v_h_4940_, v_both_4941_);
lean_dec(v_both_4941_);
return v_res_4943_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4944_; 
v___x_4944_ = 0;
return v___x_4944_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4945_; 
v___x_4945_ = 0;
return v___x_4945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4946_, uint8_t v_y_4947_){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; uint8_t v___x_4952_; 
v___x_4948_ = lean_box(v_x_4946_);
v___x_4949_ = lean_obj_tag_nat(v___x_4948_);
lean_dec(v___x_4948_);
v___x_4950_ = lean_box(v_y_4947_);
v___x_4951_ = lean_obj_tag_nat(v___x_4950_);
lean_dec(v___x_4950_);
v___x_4952_ = lean_nat_dec_eq(v___x_4949_, v___x_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4953_, lean_object* v_y_4954_){
_start:
{
uint8_t v_x_24__boxed_4955_; uint8_t v_y_25__boxed_4956_; uint8_t v_res_4957_; lean_object* v_r_4958_; 
v_x_24__boxed_4955_ = lean_unbox(v_x_4953_);
v_y_25__boxed_4956_ = lean_unbox(v_y_4954_);
v_res_4957_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_24__boxed_4955_, v_y_25__boxed_4956_);
v_r_4958_ = lean_box(v_res_4957_);
return v_r_4958_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = lean_unsigned_to_nat(2u);
v___x_4971_ = lean_nat_to_int(v___x_4970_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4972_, lean_object* v_prec_4973_){
_start:
{
lean_object* v___y_4975_; lean_object* v___y_4982_; lean_object* v___y_4989_; 
switch(v_x_4972_)
{
case 0:
{
lean_object* v___x_4995_; uint8_t v___x_4996_; 
v___x_4995_ = lean_unsigned_to_nat(1024u);
v___x_4996_ = lean_nat_dec_le(v___x_4995_, v_prec_4973_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; 
v___x_4997_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4975_ = v___x_4997_;
goto v___jp_4974_;
}
else
{
lean_object* v___x_4998_; 
v___x_4998_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4975_ = v___x_4998_;
goto v___jp_4974_;
}
}
case 1:
{
lean_object* v___x_4999_; uint8_t v___x_5000_; 
v___x_4999_ = lean_unsigned_to_nat(1024u);
v___x_5000_ = lean_nat_dec_le(v___x_4999_, v_prec_4973_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4982_ = v___x_5001_;
goto v___jp_4981_;
}
else
{
lean_object* v___x_5002_; 
v___x_5002_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4982_ = v___x_5002_;
goto v___jp_4981_;
}
}
default: 
{
lean_object* v___x_5003_; uint8_t v___x_5004_; 
v___x_5003_ = lean_unsigned_to_nat(1024u);
v___x_5004_ = lean_nat_dec_le(v___x_5003_, v_prec_4973_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; 
v___x_5005_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4989_ = v___x_5005_;
goto v___jp_4988_;
}
else
{
lean_object* v___x_5006_; 
v___x_5006_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4989_ = v___x_5006_;
goto v___jp_4988_;
}
}
}
v___jp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4976_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_4975_);
v___x_4977_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___y_4975_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
v___x_4978_ = 0;
v___x_4979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4979_, 0, v___x_4977_);
lean_ctor_set_uint8(v___x_4979_, sizeof(void*)*1, v___x_4978_);
v___x_4980_ = l_Repr_addAppParen(v___x_4979_, v_prec_4973_);
return v___x_4980_;
}
v___jp_4981_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4983_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_4982_);
v___x_4984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___y_4982_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = 0;
v___x_4986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4986_, 0, v___x_4984_);
lean_ctor_set_uint8(v___x_4986_, sizeof(void*)*1, v___x_4985_);
v___x_4987_ = l_Repr_addAppParen(v___x_4986_, v_prec_4973_);
return v___x_4987_;
}
v___jp_4988_:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4990_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_4989_);
v___x_4991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___y_4989_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = 0;
v___x_4993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4993_, 0, v___x_4991_);
lean_ctor_set_uint8(v___x_4993_, sizeof(void*)*1, v___x_4992_);
v___x_4994_ = l_Repr_addAppParen(v___x_4993_, v_prec_4973_);
return v___x_4994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_5007_, lean_object* v_prec_5008_){
_start:
{
uint8_t v_x_169__boxed_5009_; lean_object* v_res_5010_; 
v_x_169__boxed_5009_ = lean_unbox(v_x_5007_);
v_res_5010_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_169__boxed_5009_, v_prec_5008_);
lean_dec(v_prec_5008_);
return v_res_5010_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_5013_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5014_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5014_);
return v___x_5015_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5016_ = 0;
v___x_5017_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_5018_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_5019_ = lean_box(0);
v___x_5020_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
lean_ctor_set(v___x_5020_, 1, v___x_5018_);
lean_ctor_set(v___x_5020_, 2, v___x_5017_);
lean_ctor_set_uint8(v___x_5020_, sizeof(void*)*3, v___x_5016_);
return v___x_5020_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_5021_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_5023_, lean_object* v_c_5024_, lean_object* v_s_5025_, uint8_t v_behavior_5026_){
_start:
{
lean_object* v___x_5027_; lean_object* v_fst_5028_; lean_object* v_snd_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5071_; 
v___x_5027_ = l_Lean_Parser_peekToken(v_c_5024_, v_s_5025_);
v_fst_5028_ = lean_ctor_get(v___x_5027_, 0);
v_snd_5029_ = lean_ctor_get(v___x_5027_, 1);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5031_ = v___x_5027_;
v_isShared_5032_ = v_isSharedCheck_5071_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_snd_5029_);
lean_inc(v_fst_5028_);
lean_dec(v___x_5027_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5071_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v_n_5034_; 
if (lean_obj_tag(v_snd_5029_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_del_object(v___x_5031_);
lean_dec(v_fst_5028_);
v_a_5046_ = lean_ctor_get(v_snd_5029_, 0);
lean_inc(v_a_5046_);
lean_dec_ref_known(v_snd_5029_, 1);
v___x_5047_ = lean_box(0);
v___x_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5048_, 0, v_a_5046_);
lean_ctor_set(v___x_5048_, 1, v___x_5047_);
return v___x_5048_;
}
else
{
lean_object* v_a_5049_; 
v_a_5049_ = lean_ctor_get(v_snd_5029_, 0);
lean_inc(v_a_5049_);
lean_dec_ref_known(v_snd_5029_, 1);
switch(lean_obj_tag(v_a_5049_))
{
case 2:
{
lean_object* v_val_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v_val_5050_ = lean_ctor_get(v_a_5049_, 1);
lean_inc_ref(v_val_5050_);
lean_dec_ref_known(v_a_5049_, 2);
v___x_5051_ = lean_box(0);
v___x_5052_ = l_Lean_Name_str___override(v___x_5051_, v_val_5050_);
v_n_5034_ = v___x_5052_;
goto v___jp_5033_;
}
case 3:
{
switch(v_behavior_5026_)
{
case 0:
{
lean_dec_ref_known(v_a_5049_, 4);
goto v___jp_5044_;
}
case 1:
{
lean_object* v_val_5053_; lean_object* v___x_5054_; 
v_val_5053_ = lean_ctor_get(v_a_5049_, 2);
lean_inc(v_val_5053_);
lean_dec_ref_known(v_a_5049_, 4);
v___x_5054_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5023_, v_val_5053_);
lean_dec(v_val_5053_);
if (lean_obj_tag(v___x_5054_) == 0)
{
goto v___jp_5044_;
}
else
{
lean_object* v_val_5055_; lean_object* v___x_5056_; 
lean_del_object(v___x_5031_);
v_val_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_val_5055_);
lean_dec_ref_known(v___x_5054_, 1);
v___x_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5056_, 0, v_fst_5028_);
lean_ctor_set(v___x_5056_, 1, v_val_5055_);
return v___x_5056_;
}
}
default: 
{
lean_object* v_val_5057_; lean_object* v___x_5058_; 
v_val_5057_ = lean_ctor_get(v_a_5049_, 2);
lean_inc(v_val_5057_);
lean_dec_ref_known(v_a_5049_, 4);
v___x_5058_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5023_, v_val_5057_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_dec(v_val_5057_);
goto v___jp_5044_;
}
else
{
lean_object* v_val_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
lean_del_object(v___x_5031_);
v_val_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_val_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5060_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_5061_ = lean_name_eq(v_val_5057_, v___x_5060_);
lean_dec(v_val_5057_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; 
v___x_5062_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5023_, v___x_5060_);
if (lean_obj_tag(v___x_5062_) == 1)
{
lean_object* v_val_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_val_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_val_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5064_ = l_List_appendTR___redArg(v_val_5059_, v_val_5063_);
v___x_5065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5065_, 0, v_fst_5028_);
lean_ctor_set(v___x_5065_, 1, v___x_5064_);
return v___x_5065_;
}
else
{
lean_object* v___x_5066_; 
lean_dec(v___x_5062_);
v___x_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5066_, 0, v_fst_5028_);
lean_ctor_set(v___x_5066_, 1, v_val_5059_);
return v___x_5066_;
}
}
else
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5067_, 0, v_fst_5028_);
lean_ctor_set(v___x_5067_, 1, v_val_5059_);
return v___x_5067_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_5068_; 
v_kind_5068_ = lean_ctor_get(v_a_5049_, 1);
lean_inc(v_kind_5068_);
lean_dec_ref_known(v_a_5049_, 3);
v_n_5034_ = v_kind_5068_;
goto v___jp_5033_;
}
default: 
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
lean_dec(v_a_5049_);
lean_del_object(v___x_5031_);
v___x_5069_ = lean_box(0);
v___x_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5070_, 0, v_fst_5028_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
return v___x_5070_;
}
}
}
v___jp_5033_:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5023_, v_n_5034_);
lean_dec(v_n_5034_);
if (lean_obj_tag(v___x_5035_) == 1)
{
lean_object* v_val_5036_; lean_object* v___x_5038_; 
v_val_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_val_5036_);
lean_dec_ref_known(v___x_5035_, 1);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 1, v_val_5036_);
v___x_5038_ = v___x_5031_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_fst_5028_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v_val_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
else
{
lean_object* v___x_5040_; lean_object* v___x_5042_; 
lean_dec(v___x_5035_);
v___x_5040_ = lean_box(0);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 1, v___x_5040_);
v___x_5042_ = v___x_5031_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_fst_5028_);
lean_ctor_set(v_reuseFailAlloc_5043_, 1, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
v___jp_5044_:
{
lean_object* v___x_5045_; 
v___x_5045_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_5034_ = v___x_5045_;
goto v___jp_5033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_5072_, lean_object* v_c_5073_, lean_object* v_s_5074_, lean_object* v_behavior_5075_){
_start:
{
uint8_t v_behavior_boxed_5076_; lean_object* v_res_5077_; 
v_behavior_boxed_5076_ = lean_unbox(v_behavior_5075_);
v_res_5077_ = l_Lean_Parser_indexed___redArg(v_map_5072_, v_c_5073_, v_s_5074_, v_behavior_boxed_5076_);
lean_dec(v_map_5072_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_5078_, lean_object* v_map_5079_, lean_object* v_c_5080_, lean_object* v_s_5081_, uint8_t v_behavior_5082_){
_start:
{
lean_object* v___x_5083_; 
v___x_5083_ = l_Lean_Parser_indexed___redArg(v_map_5079_, v_c_5080_, v_s_5081_, v_behavior_5082_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_5084_, lean_object* v_map_5085_, lean_object* v_c_5086_, lean_object* v_s_5087_, lean_object* v_behavior_5088_){
_start:
{
uint8_t v_behavior_boxed_5089_; lean_object* v_res_5090_; 
v_behavior_boxed_5089_ = lean_unbox(v_behavior_5088_);
v_res_5090_ = l_Lean_Parser_indexed(v_00_u03b1_5084_, v_map_5085_, v_c_5086_, v_s_5087_, v_behavior_boxed_5089_);
lean_dec(v_map_5085_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v___x_5094_; 
v___x_5094_ = l_Lean_Parser_whitespace(v___y_5092_, v___y_5093_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_5095_, v___y_5096_, v___y_5097_);
lean_dec(v_x_5095_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___f_5101_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_5102_ = lean_st_mk_ref(v___f_5101_);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_5106_){
_start:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5108_ = lean_st_ref_get(v___x_5106_);
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_5110_);
lean_dec(v___x_5110_);
return v_res_5112_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5113_; lean_object* v___f_5114_; 
v___x_5113_ = l_Lean_Parser_categoryParserFnRef;
v___f_5114_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5114_, 0, v___x_5113_);
return v___f_5114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; uint8_t v___x_5125_; lean_object* v___x_5126_; 
v___f_5121_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_5122_ = lean_box(0);
v___x_5123_ = lean_box(2);
v___x_5124_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_));
v___x_5125_ = 0;
v___x_5126_ = l_Lean_registerEnvExtension___redArg(v___f_5121_, v___x_5122_, v___x_5123_, v___x_5124_, v___x_5125_, v___x_5125_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_5130_, v___y_5131_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_5133_, v___y_5134_, v___y_5135_);
lean_dec_ref(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v_a_5133_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_5140_, lean_object* v_ctx_5141_, lean_object* v_s_5142_){
_start:
{
lean_object* v_toParserModuleContext_5143_; lean_object* v_env_5144_; lean_object* v___x_5145_; lean_object* v_asyncMode_5146_; lean_object* v___f_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; lean_object* v___x_21__overap_5150_; lean_object* v___x_5151_; 
v_toParserModuleContext_5143_ = lean_ctor_get(v_ctx_5141_, 1);
v_env_5144_ = lean_ctor_get(v_toParserModuleContext_5143_, 0);
v___x_5145_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_5146_ = lean_ctor_get(v___x_5145_, 2);
v___f_5147_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_5148_ = lean_box(0);
v___x_5149_ = 0;
lean_inc_ref(v_env_5144_);
v___x_21__overap_5150_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_5147_, v___x_5145_, v_env_5144_, v_asyncMode_5146_, v___x_5148_, v___x_5149_);
v___x_5151_ = lean_apply_3(v___x_21__overap_5150_, v_catName_5140_, v_ctx_5141_, v_s_5142_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_5152_, lean_object* v_x_5153_){
_start:
{
lean_object* v_quotDepth_5154_; uint8_t v_suppressInsideQuot_5155_; lean_object* v_savedPos_x3f_5156_; lean_object* v_forbiddenTks_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
v_quotDepth_5154_ = lean_ctor_get(v_x_5153_, 1);
v_suppressInsideQuot_5155_ = lean_ctor_get_uint8(v_x_5153_, sizeof(void*)*4);
v_savedPos_x3f_5156_ = lean_ctor_get(v_x_5153_, 2);
v_forbiddenTks_5157_ = lean_ctor_get(v_x_5153_, 3);
v_isSharedCheck_5164_ = !lean_is_exclusive(v_x_5153_);
if (v_isSharedCheck_5164_ == 0)
{
lean_object* v_unused_5165_; 
v_unused_5165_ = lean_ctor_get(v_x_5153_, 0);
lean_dec(v_unused_5165_);
v___x_5159_ = v_x_5153_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_forbiddenTks_5157_);
lean_inc(v_savedPos_x3f_5156_);
lean_inc(v_quotDepth_5154_);
lean_dec(v_x_5153_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
lean_ctor_set(v___x_5159_, 0, v_prec_5152_);
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_prec_5152_);
lean_ctor_set(v_reuseFailAlloc_5163_, 1, v_quotDepth_5154_);
lean_ctor_set(v_reuseFailAlloc_5163_, 2, v_savedPos_x3f_5156_);
lean_ctor_set(v_reuseFailAlloc_5163_, 3, v_forbiddenTks_5157_);
lean_ctor_set_uint8(v_reuseFailAlloc_5163_, sizeof(void*)*4, v_suppressInsideQuot_5155_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_5166_, lean_object* v_prec_5167_){
_start:
{
lean_object* v___f_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___f_5168_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_5168_, 0, v_prec_5167_);
v___x_5169_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_5166_);
v___x_5170_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_5170_, 0, v_catName_5166_);
v___x_5171_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_5171_, 0, v_catName_5166_);
lean_closure_set(v___x_5171_, 1, v___x_5170_);
v___x_5172_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5172_, 0, v___f_5168_);
lean_closure_set(v___x_5172_, 1, v___x_5171_);
v___x_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5169_);
lean_ctor_set(v___x_5173_, 1, v___x_5172_);
return v___x_5173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5177_){
_start:
{
lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5178_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5179_ = l_Lean_Parser_categoryParser(v___x_5178_, v_prec_5177_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5181_, lean_object* v_s_5182_){
_start:
{
lean_object* v_stxStack_5183_; lean_object* v_pos_5184_; lean_object* v_prev_5185_; uint8_t v___x_5186_; 
v_stxStack_5183_ = lean_ctor_get(v_s_5182_, 0);
v_pos_5184_ = lean_ctor_get(v_s_5182_, 2);
v_prev_5185_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5183_);
v___x_5186_ = l_Lean_Parser_checkTailNoWs(v_prev_5185_);
lean_dec(v_prev_5185_);
if (v___x_5186_ == 0)
{
return v_s_5182_;
}
else
{
lean_object* v_toInputContext_5187_; uint8_t v___x_5188_; 
v_toInputContext_5187_ = lean_ctor_get(v_c_5181_, 0);
v___x_5188_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5187_, v_pos_5184_);
if (v___x_5188_ == 0)
{
lean_object* v_inputString_5189_; uint32_t v_curr_5190_; uint32_t v___x_5191_; uint8_t v___x_5192_; 
v_inputString_5189_ = lean_ctor_get(v_toInputContext_5187_, 0);
v_curr_5190_ = lean_string_utf8_get_fast(v_inputString_5189_, v_pos_5184_);
v___x_5191_ = 58;
v___x_5192_ = lean_uint32_dec_eq(v_curr_5190_, v___x_5191_);
if (v___x_5192_ == 0)
{
return v_s_5182_;
}
else
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5193_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5194_ = lean_box(0);
v___x_5195_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5182_, v___x_5193_, v___x_5194_, v___x_5192_);
return v___x_5195_;
}
}
else
{
return v_s_5182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5196_, lean_object* v_s_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5196_, v_s_5197_);
lean_dec_ref(v_c_5196_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5211_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5212_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5213_ = l_Lean_addBuiltinDocString(v___x_5211_, v___x_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5216_, lean_object* v_p_5217_, lean_object* v_c_5218_, lean_object* v_s_5219_){
_start:
{
lean_object* v___x_5220_; lean_object* v_errorMsg_5221_; 
v___x_5220_ = lean_apply_2(v_p_5217_, v_c_5218_, v_s_5219_);
v_errorMsg_5221_ = lean_ctor_get(v___x_5220_, 4);
lean_inc(v_errorMsg_5221_);
if (lean_obj_tag(v_errorMsg_5221_) == 1)
{
lean_object* v_val_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5252_; 
v_val_5222_ = lean_ctor_get(v_errorMsg_5221_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v_errorMsg_5221_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5224_ = v_errorMsg_5221_;
v_isShared_5225_ = v_isSharedCheck_5252_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_val_5222_);
lean_dec(v_errorMsg_5221_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5252_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v_stxStack_5226_; lean_object* v_lhsPrec_5227_; lean_object* v_pos_5228_; lean_object* v_cache_5229_; lean_object* v_recoveredErrors_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5250_; 
v_stxStack_5226_ = lean_ctor_get(v___x_5220_, 0);
v_lhsPrec_5227_ = lean_ctor_get(v___x_5220_, 1);
v_pos_5228_ = lean_ctor_get(v___x_5220_, 2);
v_cache_5229_ = lean_ctor_get(v___x_5220_, 3);
v_recoveredErrors_5230_ = lean_ctor_get(v___x_5220_, 5);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5250_ == 0)
{
lean_object* v_unused_5251_; 
v_unused_5251_ = lean_ctor_get(v___x_5220_, 4);
lean_dec(v_unused_5251_);
v___x_5232_ = v___x_5220_;
v_isShared_5233_ = v_isSharedCheck_5250_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_recoveredErrors_5230_);
lean_inc(v_cache_5229_);
lean_inc(v_pos_5228_);
lean_inc(v_lhsPrec_5227_);
lean_inc(v_stxStack_5226_);
lean_dec(v___x_5220_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5250_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v_unexpectedTk_5234_; lean_object* v_unexpected_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5248_; 
v_unexpectedTk_5234_ = lean_ctor_get(v_val_5222_, 0);
v_unexpected_5235_ = lean_ctor_get(v_val_5222_, 1);
v_isSharedCheck_5248_ = !lean_is_exclusive(v_val_5222_);
if (v_isSharedCheck_5248_ == 0)
{
lean_object* v_unused_5249_; 
v_unused_5249_ = lean_ctor_get(v_val_5222_, 2);
lean_dec(v_unused_5249_);
v___x_5237_ = v_val_5222_;
v_isShared_5238_ = v_isSharedCheck_5248_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_unexpected_5235_);
lean_inc(v_unexpectedTk_5234_);
lean_dec(v_val_5222_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5248_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
lean_ctor_set(v___x_5237_, 2, v_expected_5216_);
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_unexpectedTk_5234_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_unexpected_5235_);
lean_ctor_set(v_reuseFailAlloc_5247_, 2, v_expected_5216_);
v___x_5240_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
lean_object* v___x_5242_; 
if (v_isShared_5225_ == 0)
{
lean_ctor_set(v___x_5224_, 0, v___x_5240_);
v___x_5242_ = v___x_5224_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5240_);
v___x_5242_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
lean_object* v___x_5244_; 
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 4, v___x_5242_);
v___x_5244_ = v___x_5232_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_stxStack_5226_);
lean_ctor_set(v_reuseFailAlloc_5245_, 1, v_lhsPrec_5227_);
lean_ctor_set(v_reuseFailAlloc_5245_, 2, v_pos_5228_);
lean_ctor_set(v_reuseFailAlloc_5245_, 3, v_cache_5229_);
lean_ctor_set(v_reuseFailAlloc_5245_, 4, v___x_5242_);
lean_ctor_set(v_reuseFailAlloc_5245_, 5, v_recoveredErrors_5230_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5221_);
lean_dec(v_expected_5216_);
return v___x_5220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5253_, lean_object* v_p_5254_){
_start:
{
lean_object* v_info_5255_; lean_object* v_fn_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5264_; 
v_info_5255_ = lean_ctor_get(v_p_5254_, 0);
v_fn_5256_ = lean_ctor_get(v_p_5254_, 1);
v_isSharedCheck_5264_ = !lean_is_exclusive(v_p_5254_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5258_ = v_p_5254_;
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_fn_5256_);
lean_inc(v_info_5255_);
lean_dec(v_p_5254_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5260_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5260_, 0, v_expected_5253_);
lean_closure_set(v___x_5260_, 1, v_fn_5256_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 1, v___x_5260_);
v___x_5262_ = v___x_5258_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_info_5255_);
lean_ctor_set(v_reuseFailAlloc_5263_, 1, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5265_, lean_object* v_s_5266_){
_start:
{
lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5267_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_5268_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5266_, v___x_5267_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5269_, lean_object* v_s_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_Parser_pushNone___lam__0(v_x_5269_, v_s_5270_);
lean_dec_ref(v_x_5269_);
return v_res_5271_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5281_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5282_ = l_Lean_Parser_symbolNoAntiquot(v___x_5281_);
return v___x_5282_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5283_ = lean_unsigned_to_nat(0u);
v___x_5284_ = l_Lean_Parser_termParser(v___x_5283_);
return v___x_5284_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5285_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5286_ = l_Lean_Parser_decQuotDepth(v___x_5285_);
return v___x_5286_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5288_ = l_Lean_Parser_symbolNoAntiquot(v___x_5287_);
return v___x_5288_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; 
v___x_5289_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5290_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5291_ = l_Lean_Parser_andthen(v___x_5290_, v___x_5289_);
return v___x_5291_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5292_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5293_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5294_ = l_Lean_Parser_andthen(v___x_5293_, v___x_5292_);
return v___x_5294_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v___x_5295_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5296_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5297_ = l_Lean_Parser_node(v___x_5296_, v___x_5295_);
return v___x_5297_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5298_; 
v___x_5298_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5298_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5301_ = l_Lean_Parser_symbolNoAntiquot(v___x_5300_);
return v___x_5301_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5302_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5303_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5304_ = l_Lean_Parser_orelse(v___x_5303_, v___x_5302_);
return v___x_5304_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5305_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5306_ = l_Lean_Parser_identNoAntiquot;
v___x_5307_ = l_Lean_Parser_orelse(v___x_5306_, v___x_5305_);
return v___x_5307_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5308_; 
v___x_5308_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5308_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5310_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5311_ = l_Lean_Parser_checkNoWsBefore(v___x_5310_);
return v___x_5311_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5313_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5314_ = l_Lean_Parser_symbolNoAntiquot(v___x_5313_);
return v___x_5314_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5316_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5317_ = l_Lean_Parser_symbolNoAntiquot(v___x_5316_);
return v___x_5317_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v___x_5318_ = l_Lean_Parser_antiquotExpr;
v___x_5319_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5320_ = l_Lean_Parser_andthen(v___x_5319_, v___x_5318_);
return v___x_5320_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
v___x_5321_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5322_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5323_ = l_Lean_Parser_andthen(v___x_5322_, v___x_5321_);
return v___x_5323_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; 
v___x_5324_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5325_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5326_ = l_Lean_Parser_andthen(v___x_5325_, v___x_5324_);
return v___x_5326_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
v___x_5327_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5328_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5329_ = l_Lean_Parser_andthen(v___x_5328_, v___x_5327_);
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5333_, lean_object* v_s_5334_){
_start:
{
lean_object* v_pos_5335_; lean_object* v_errorMsg_5336_; lean_object* v___x_5337_; uint8_t v___x_5338_; 
v_pos_5335_ = lean_ctor_get(v_s_5334_, 2);
v_errorMsg_5336_ = lean_ctor_get(v_s_5334_, 4);
v___x_5337_ = lean_box(0);
v___x_5338_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5336_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_dec_ref(v_c_5333_);
return v_s_5334_;
}
else
{
lean_object* v___x_5339_; lean_object* v_fn_5340_; lean_object* v_iniSz_5341_; lean_object* v_s_5342_; lean_object* v_errorMsg_5343_; uint8_t v___x_5344_; 
lean_inc(v_pos_5335_);
v___x_5339_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5340_ = lean_ctor_get(v___x_5339_, 1);
v_iniSz_5341_ = l_Lean_Parser_ParserState_stackSize(v_s_5334_);
lean_inc_ref(v_fn_5340_);
v_s_5342_ = lean_apply_2(v_fn_5340_, v_c_5333_, v_s_5334_);
v_errorMsg_5343_ = lean_ctor_get(v_s_5342_, 4);
lean_inc(v_errorMsg_5343_);
v___x_5344_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5343_, v___x_5337_);
lean_dec(v_errorMsg_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; 
v___x_5345_ = l_Lean_Parser_ParserState_restore(v_s_5342_, v_iniSz_5341_, v_pos_5335_);
lean_dec(v_iniSz_5341_);
return v___x_5345_;
}
else
{
lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; 
lean_dec(v_pos_5335_);
v___x_5346_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5347_ = lean_unsigned_to_nat(1u);
v___x_5348_ = lean_nat_sub(v_iniSz_5341_, v___x_5347_);
lean_dec(v_iniSz_5341_);
v___x_5349_ = l_Lean_Parser_ParserState_mkNode(v_s_5342_, v___x_5346_, v___x_5348_);
lean_dec(v___x_5348_);
return v___x_5349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v_toInputContext_5353_; lean_object* v_s_5354_; lean_object* v_pos_5355_; lean_object* v_inputString_5356_; uint32_t v___x_5357_; uint32_t v___x_5358_; uint8_t v___x_5359_; 
v_toInputContext_5353_ = lean_ctor_get(v___y_5351_, 0);
lean_inc_ref(v___y_5351_);
v_s_5354_ = lean_apply_2(v_fn_5350_, v___y_5351_, v___y_5352_);
v_pos_5355_ = lean_ctor_get(v_s_5354_, 2);
lean_inc(v_pos_5355_);
v_inputString_5356_ = lean_ctor_get(v_toInputContext_5353_, 0);
v___x_5357_ = lean_string_utf8_get(v_inputString_5356_, v_pos_5355_);
lean_dec(v_pos_5355_);
v___x_5358_ = 37;
v___x_5359_ = lean_uint32_dec_eq(v___x_5357_, v___x_5358_);
if (v___x_5359_ == 0)
{
lean_dec_ref(v___y_5351_);
return v_s_5354_;
}
else
{
lean_object* v___x_5360_; 
v___x_5360_ = l_Lean_Parser_tokenAntiquotFn(v___y_5351_, v_s_5354_);
return v___x_5360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5361_){
_start:
{
lean_object* v_info_5362_; lean_object* v_fn_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5371_; 
v_info_5362_ = lean_ctor_get(v_p_5361_, 0);
v_fn_5363_ = lean_ctor_get(v_p_5361_, 1);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_p_5361_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5365_ = v_p_5361_;
v_isShared_5366_ = v_isSharedCheck_5371_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_fn_5363_);
lean_inc(v_info_5362_);
lean_dec(v_p_5361_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5371_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___f_5367_; lean_object* v___x_5369_; 
v___f_5367_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5367_, 0, v_fn_5363_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 1, v___f_5367_);
v___x_5369_ = v___x_5365_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_info_5362_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v___f_5367_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5372_){
_start:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; 
v___x_5373_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5372_);
v___x_5374_ = l_Lean_Parser_tokenWithAntiquot(v___x_5373_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5377_, uint8_t v_includeIdent_5378_){
_start:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5379_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5377_, v_includeIdent_5378_);
v___x_5380_ = l_Lean_Parser_tokenWithAntiquot(v___x_5379_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5381_, lean_object* v_includeIdent_5382_){
_start:
{
uint8_t v_includeIdent_boxed_5383_; lean_object* v_res_5384_; 
v_includeIdent_boxed_5383_ = lean_unbox(v_includeIdent_5382_);
v_res_5384_ = l_Lean_Parser_nonReservedSymbol(v_sym_5381_, v_includeIdent_boxed_5383_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5385_, lean_object* v_asciiSym_5386_){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5387_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5385_, v_asciiSym_5386_);
v___x_5388_ = l_Lean_Parser_tokenWithAntiquot(v___x_5387_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5389_, lean_object* v_asciiSym_5390_, uint8_t v_preserveForPP_5391_){
_start:
{
lean_object* v___x_5392_; 
v___x_5392_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5389_, v_asciiSym_5390_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5393_, lean_object* v_asciiSym_5394_, lean_object* v_preserveForPP_5395_){
_start:
{
uint8_t v_preserveForPP_boxed_5396_; lean_object* v_res_5397_; 
v_preserveForPP_boxed_5396_ = lean_unbox(v_preserveForPP_5395_);
v_res_5397_ = l_Lean_Parser_unicodeSymbol(v_sym_5393_, v_asciiSym_5394_, v_preserveForPP_boxed_5396_);
return v_res_5397_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5398_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5399_ = l_Lean_Parser_symbol(v___x_5398_);
return v___x_5399_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5400_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5401_ = lean_box(0);
v___x_5402_ = l_Lean_Parser_setExpected(v___x_5401_, v___x_5400_);
return v___x_5402_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5404_ = l_Lean_Parser_checkNoWsBefore(v___x_5403_);
return v___x_5404_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5405_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5406_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5407_ = l_Lean_Parser_andthen(v___x_5406_, v___x_5405_);
return v___x_5407_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5408_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5409_ = l_Lean_Parser_manyNoAntiquot(v___x_5408_);
return v___x_5409_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5412_ = l_Lean_Parser_checkNoWsBefore(v___x_5411_);
return v___x_5412_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; 
v___x_5421_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5422_ = l_Lean_Parser_symbol(v___x_5421_);
return v___x_5422_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5423_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5424_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5425_ = l_Lean_Parser_andthen(v___x_5424_, v___x_5423_);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5429_, lean_object* v_kind_5430_, uint8_t v_anonymous_5431_, uint8_t v_isPseudoKind_5432_){
_start:
{
lean_object* v___y_5434_; lean_object* v___y_5435_; lean_object* v___y_5448_; 
if (v_isPseudoKind_5432_ == 0)
{
lean_object* v___x_5466_; 
v___x_5466_ = lean_box(0);
v___y_5448_ = v___x_5466_;
goto v___jp_5447_;
}
else
{
lean_object* v___x_5467_; 
v___x_5467_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5448_ = v___x_5467_;
goto v___jp_5447_;
}
v___jp_5433_:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_5436_ = l_Lean_Parser_maxPrec;
v___x_5437_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5438_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5439_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5440_ = l_Lean_Parser_antiquotExpr;
v___x_5441_ = l_Lean_Parser_andthen(v___x_5440_, v___y_5435_);
v___x_5442_ = l_Lean_Parser_andthen(v___x_5439_, v___x_5441_);
v___x_5443_ = l_Lean_Parser_andthen(v___x_5438_, v___x_5442_);
v___x_5444_ = l_Lean_Parser_andthen(v___x_5437_, v___x_5443_);
v___x_5445_ = l_Lean_Parser_atomic(v___x_5444_);
v___x_5446_ = l_Lean_Parser_leadingNode(v___y_5434_, v___x_5436_, v___x_5445_);
return v___x_5446_;
}
v___jp_5447_:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v_kind_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; uint8_t v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v_nameP_5463_; 
lean_inc(v___y_5448_);
v___x_5449_ = l_Lean_Name_append(v_kind_5430_, v___y_5448_);
v___x_5450_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5451_ = l_Lean_Name_append(v___x_5449_, v___x_5450_);
v___x_5452_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5453_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5454_ = lean_string_append(v___x_5453_, v_name_5429_);
v___x_5455_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5456_ = lean_string_append(v___x_5454_, v___x_5455_);
v___x_5457_ = l_Lean_Parser_checkNoWsBefore(v___x_5456_);
v___x_5458_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5459_ = 0;
v___x_5460_ = l_Lean_Parser_nonReservedSymbol(v_name_5429_, v___x_5459_);
v___x_5461_ = l_Lean_Parser_andthen(v___x_5458_, v___x_5460_);
v___x_5462_ = l_Lean_Parser_andthen(v___x_5457_, v___x_5461_);
v_nameP_5463_ = l_Lean_Parser_node(v___x_5452_, v___x_5462_);
if (v_anonymous_5431_ == 0)
{
v___y_5434_ = v_kind_5451_;
v___y_5435_ = v_nameP_5463_;
goto v___jp_5433_;
}
else
{
lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5464_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5465_ = l_Lean_Parser_orelse(v_nameP_5463_, v___x_5464_);
v___y_5434_ = v_kind_5451_;
v___y_5435_ = v___x_5465_;
goto v___jp_5433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5468_, lean_object* v_kind_5469_, lean_object* v_anonymous_5470_, lean_object* v_isPseudoKind_5471_){
_start:
{
uint8_t v_anonymous_boxed_5472_; uint8_t v_isPseudoKind_boxed_5473_; lean_object* v_res_5474_; 
v_anonymous_boxed_5472_ = lean_unbox(v_anonymous_5470_);
v_isPseudoKind_boxed_5473_ = lean_unbox(v_isPseudoKind_5471_);
v_res_5474_ = l_Lean_Parser_mkAntiquot(v_name_5468_, v_kind_5469_, v_anonymous_boxed_5472_, v_isPseudoKind_boxed_5473_);
return v_res_5474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5482_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5483_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5484_ = l_Lean_addBuiltinDocString(v___x_5482_, v___x_5483_);
return v___x_5484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5487_, lean_object* v_p_5488_, uint8_t v_antiquotBehavior_5489_, lean_object* v_c_5490_, lean_object* v_s_5491_){
_start:
{
lean_object* v_toInputContext_5492_; lean_object* v_pos_5493_; lean_object* v_inputString_5494_; uint32_t v___x_5495_; uint32_t v___x_5496_; uint8_t v___x_5497_; 
v_toInputContext_5492_ = lean_ctor_get(v_c_5490_, 0);
v_pos_5493_ = lean_ctor_get(v_s_5491_, 2);
v_inputString_5494_ = lean_ctor_get(v_toInputContext_5492_, 0);
v___x_5495_ = lean_string_utf8_get(v_inputString_5494_, v_pos_5493_);
v___x_5496_ = 36;
v___x_5497_ = lean_uint32_dec_eq(v___x_5495_, v___x_5496_);
if (v___x_5497_ == 0)
{
lean_object* v___x_5498_; 
lean_dec_ref(v_antiquotP_5487_);
v___x_5498_ = lean_apply_2(v_p_5488_, v_c_5490_, v_s_5491_);
return v___x_5498_;
}
else
{
lean_object* v___x_5499_; 
v___x_5499_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5487_, v_p_5488_, v_antiquotBehavior_5489_, v_c_5490_, v_s_5491_);
return v___x_5499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5500_, lean_object* v_p_5501_, lean_object* v_antiquotBehavior_5502_, lean_object* v_c_5503_, lean_object* v_s_5504_){
_start:
{
uint8_t v_antiquotBehavior_boxed_5505_; lean_object* v_res_5506_; 
v_antiquotBehavior_boxed_5505_ = lean_unbox(v_antiquotBehavior_5502_);
v_res_5506_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5500_, v_p_5501_, v_antiquotBehavior_boxed_5505_, v_c_5503_, v_s_5504_);
return v_res_5506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5507_, lean_object* v_p_5508_){
_start:
{
lean_object* v_info_5509_; lean_object* v_fn_5510_; lean_object* v_info_5511_; lean_object* v_fn_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5523_; 
v_info_5509_ = lean_ctor_get(v_antiquotP_5507_, 0);
lean_inc_ref(v_info_5509_);
v_fn_5510_ = lean_ctor_get(v_antiquotP_5507_, 1);
lean_inc_ref(v_fn_5510_);
lean_dec_ref(v_antiquotP_5507_);
v_info_5511_ = lean_ctor_get(v_p_5508_, 0);
v_fn_5512_ = lean_ctor_get(v_p_5508_, 1);
v_isSharedCheck_5523_ = !lean_is_exclusive(v_p_5508_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5514_ = v_p_5508_;
v_isShared_5515_ = v_isSharedCheck_5523_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_fn_5512_);
lean_inc(v_info_5511_);
lean_dec(v_p_5508_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5523_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5516_; uint8_t v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5521_; 
v___x_5516_ = l_Lean_Parser_orelseInfo(v_info_5509_, v_info_5511_);
v___x_5517_ = 1;
v___x_5518_ = lean_box(v___x_5517_);
v___x_5519_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5519_, 0, v_fn_5510_);
lean_closure_set(v___x_5519_, 1, v_fn_5512_);
lean_closure_set(v___x_5519_, 2, v___x_5518_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5519_);
lean_ctor_set(v___x_5514_, 0, v___x_5516_);
v___x_5521_ = v___x_5514_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5516_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5519_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5531_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5532_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5533_ = l_Lean_addBuiltinDocString(v___x_5531_, v___x_5532_);
return v___x_5533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotAcceptLhs(lean_object* v_antiquotP_5536_, lean_object* v_p_5537_){
_start:
{
lean_object* v_info_5538_; lean_object* v_fn_5539_; lean_object* v_info_5540_; lean_object* v_fn_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5552_; 
v_info_5538_ = lean_ctor_get(v_antiquotP_5536_, 0);
lean_inc_ref(v_info_5538_);
v_fn_5539_ = lean_ctor_get(v_antiquotP_5536_, 1);
lean_inc_ref(v_fn_5539_);
lean_dec_ref(v_antiquotP_5536_);
v_info_5540_ = lean_ctor_get(v_p_5537_, 0);
v_fn_5541_ = lean_ctor_get(v_p_5537_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_p_5537_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5543_ = v_p_5537_;
v_isShared_5544_ = v_isSharedCheck_5552_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_fn_5541_);
lean_inc(v_info_5540_);
lean_dec(v_p_5537_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5552_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5545_; uint8_t v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
v___x_5545_ = l_Lean_Parser_orelseInfo(v_info_5538_, v_info_5540_);
v___x_5546_ = 0;
v___x_5547_ = lean_box(v___x_5546_);
v___x_5548_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5548_, 0, v_fn_5539_);
lean_closure_set(v___x_5548_, 1, v_fn_5541_);
lean_closure_set(v___x_5548_, 2, v___x_5547_);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 1, v___x_5548_);
lean_ctor_set(v___x_5543_, 0, v___x_5545_);
v___x_5550_ = v___x_5543_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5545_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v___x_5548_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1(){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
v___x_5560_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1));
v___x_5561_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__2));
v___x_5562_ = l_Lean_addBuiltinDocString(v___x_5560_, v___x_5561_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___boxed(lean_object* v_a_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1();
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5565_){
_start:
{
lean_object* v_fn_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5574_; 
v_fn_5566_ = lean_ctor_get(v_p_5565_, 1);
v_isSharedCheck_5574_ = !lean_is_exclusive(v_p_5565_);
if (v_isSharedCheck_5574_ == 0)
{
lean_object* v_unused_5575_; 
v_unused_5575_ = lean_ctor_get(v_p_5565_, 0);
lean_dec(v_unused_5575_);
v___x_5568_ = v_p_5565_;
v_isShared_5569_ = v_isSharedCheck_5574_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_fn_5566_);
lean_dec(v_p_5565_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5574_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5570_; lean_object* v___x_5572_; 
v___x_5570_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v___x_5570_);
v___x_5572_ = v___x_5568_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v_fn_5566_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5579_; lean_object* v___x_5580_; 
v___x_5579_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5580_ = l_Lean_Parser_symbol(v___x_5579_);
return v___x_5580_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5581_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5582_ = l_Lean_Parser_symbol(v___x_5581_);
return v___x_5582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5583_, lean_object* v_p_5584_, lean_object* v_suffix_5585_){
_start:
{
lean_object* v___x_5586_; lean_object* v_kind_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; 
v___x_5586_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5587_ = l_Lean_Name_append(v_kind_5583_, v___x_5586_);
v___x_5588_ = l_Lean_Parser_maxPrec;
v___x_5589_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5590_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5591_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5592_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5593_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5594_ = l_Lean_Parser_node(v___x_5593_, v_p_5584_);
v___x_5595_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5596_ = l_Lean_Parser_andthen(v___x_5595_, v_suffix_5585_);
v___x_5597_ = l_Lean_Parser_andthen(v___x_5594_, v___x_5596_);
v___x_5598_ = l_Lean_Parser_andthen(v___x_5592_, v___x_5597_);
v___x_5599_ = l_Lean_Parser_andthen(v___x_5591_, v___x_5598_);
v___x_5600_ = l_Lean_Parser_andthen(v___x_5590_, v___x_5599_);
v___x_5601_ = l_Lean_Parser_andthen(v___x_5589_, v___x_5600_);
v___x_5602_ = l_Lean_Parser_atomic(v___x_5601_);
v___x_5603_ = l_Lean_Parser_leadingNode(v_kind_5587_, v___x_5588_, v___x_5602_);
return v___x_5603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5611_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5612_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5613_ = l_Lean_addBuiltinDocString(v___x_5611_, v___x_5612_);
return v___x_5613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5619_, lean_object* v_suffix_5620_, lean_object* v_c_5621_, lean_object* v_s_5622_){
_start:
{
lean_object* v_pos_5623_; lean_object* v_iniSz_5624_; lean_object* v_s_5625_; lean_object* v_stxStack_5626_; lean_object* v_errorMsg_5627_; lean_object* v___x_5628_; uint8_t v___x_5629_; 
v_pos_5623_ = lean_ctor_get(v_s_5622_, 2);
lean_inc(v_pos_5623_);
v_iniSz_5624_ = l_Lean_Parser_ParserState_stackSize(v_s_5622_);
v_s_5625_ = lean_apply_2(v_suffix_5620_, v_c_5621_, v_s_5622_);
v_stxStack_5626_ = lean_ctor_get(v_s_5625_, 0);
lean_inc_ref(v_stxStack_5626_);
v_errorMsg_5627_ = lean_ctor_get(v_s_5625_, 4);
lean_inc(v_errorMsg_5627_);
v___x_5628_ = lean_box(0);
v___x_5629_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5627_, v___x_5628_);
lean_dec(v_errorMsg_5627_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; 
lean_dec_ref(v_stxStack_5626_);
lean_dec(v_kind_5619_);
v___x_5630_ = l_Lean_Parser_ParserState_restore(v_s_5625_, v_iniSz_5624_, v_pos_5623_);
lean_dec(v_iniSz_5624_);
return v___x_5630_;
}
else
{
lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; 
lean_dec(v_iniSz_5624_);
lean_dec(v_pos_5623_);
v___x_5631_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5632_ = l_Lean_Name_append(v_kind_5619_, v___x_5631_);
v___x_5633_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5626_);
lean_dec_ref(v_stxStack_5626_);
v___x_5634_ = lean_unsigned_to_nat(2u);
v___x_5635_ = lean_nat_sub(v___x_5633_, v___x_5634_);
lean_dec(v___x_5633_);
v___x_5636_ = l_Lean_Parser_ParserState_mkNode(v_s_5625_, v___x_5632_, v___x_5635_);
lean_dec(v___x_5635_);
return v___x_5636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5637_, lean_object* v_kind_5638_, lean_object* v_fn_5639_, lean_object* v_c_5640_, lean_object* v_s_5641_){
_start:
{
lean_object* v_s_5642_; lean_object* v_stxStack_5643_; lean_object* v_errorMsg_5644_; lean_object* v___x_5645_; uint8_t v___x_5646_; 
lean_inc_ref(v_c_5640_);
v_s_5642_ = lean_apply_2(v_fn_5637_, v_c_5640_, v_s_5641_);
v_stxStack_5643_ = lean_ctor_get(v_s_5642_, 0);
lean_inc_ref(v_stxStack_5643_);
v_errorMsg_5644_ = lean_ctor_get(v_s_5642_, 4);
lean_inc(v_errorMsg_5644_);
v___x_5645_ = lean_box(0);
v___x_5646_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5644_, v___x_5645_);
lean_dec(v_errorMsg_5644_);
if (v___x_5646_ == 0)
{
lean_dec_ref(v_stxStack_5643_);
lean_dec_ref(v_c_5640_);
lean_dec_ref(v_fn_5639_);
lean_dec(v_kind_5638_);
return v_s_5642_;
}
else
{
lean_object* v___x_5647_; uint8_t v___x_5648_; 
v___x_5647_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5643_);
lean_dec_ref(v_stxStack_5643_);
v___x_5648_ = l_Lean_Syntax_isAntiquots(v___x_5647_);
if (v___x_5648_ == 0)
{
lean_dec_ref(v_c_5640_);
lean_dec_ref(v_fn_5639_);
lean_dec(v_kind_5638_);
return v_s_5642_;
}
else
{
lean_object* v___x_5649_; 
v___x_5649_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5638_, v_fn_5639_, v_c_5640_, v_s_5642_);
return v___x_5649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5650_, lean_object* v_p_5651_, lean_object* v_suffix_5652_){
_start:
{
lean_object* v_info_5653_; lean_object* v_fn_5654_; lean_object* v_info_5655_; lean_object* v_fn_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5665_; 
v_info_5653_ = lean_ctor_get(v_p_5651_, 0);
lean_inc_ref(v_info_5653_);
v_fn_5654_ = lean_ctor_get(v_p_5651_, 1);
lean_inc_ref(v_fn_5654_);
lean_dec_ref(v_p_5651_);
v_info_5655_ = lean_ctor_get(v_suffix_5652_, 0);
v_fn_5656_ = lean_ctor_get(v_suffix_5652_, 1);
v_isSharedCheck_5665_ = !lean_is_exclusive(v_suffix_5652_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5658_ = v_suffix_5652_;
v_isShared_5659_ = v_isSharedCheck_5665_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_fn_5656_);
lean_inc(v_info_5655_);
lean_dec(v_suffix_5652_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5665_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___f_5660_; lean_object* v___x_5661_; lean_object* v___x_5663_; 
v___f_5660_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5660_, 0, v_fn_5654_);
lean_closure_set(v___f_5660_, 1, v_kind_5650_);
lean_closure_set(v___f_5660_, 2, v_fn_5656_);
v___x_5661_ = l_Lean_Parser_andthenInfo(v_info_5653_, v_info_5655_);
if (v_isShared_5659_ == 0)
{
lean_ctor_set(v___x_5658_, 1, v___f_5660_);
lean_ctor_set(v___x_5658_, 0, v___x_5661_);
v___x_5663_ = v___x_5658_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v___x_5661_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v___f_5660_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5673_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5674_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5675_ = l_Lean_addBuiltinDocString(v___x_5673_, v___x_5674_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5676_){
_start:
{
lean_object* v_res_5677_; 
v_res_5677_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5678_, lean_object* v_p_5679_, lean_object* v_suffix_5680_){
_start:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; 
lean_inc_ref(v_p_5679_);
v___x_5681_ = l_Lean_Parser_withoutInfo(v_p_5679_);
lean_inc_ref(v_suffix_5680_);
lean_inc(v_kind_5678_);
v___x_5682_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5678_, v___x_5681_, v_suffix_5680_);
v___x_5683_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5678_, v_p_5679_, v_suffix_5680_);
v___x_5684_ = l_Lean_Parser_withAntiquot(v___x_5682_, v___x_5683_);
return v___x_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5685_, lean_object* v_kind_5686_, lean_object* v_p_5687_, uint8_t v_anonymous_5688_){
_start:
{
uint8_t v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5689_ = 0;
lean_inc(v_kind_5686_);
v___x_5690_ = l_Lean_Parser_mkAntiquot(v_name_5685_, v_kind_5686_, v_anonymous_5688_, v___x_5689_);
v___x_5691_ = l_Lean_Parser_node(v_kind_5686_, v_p_5687_);
v___x_5692_ = l_Lean_Parser_withAntiquot(v___x_5690_, v___x_5691_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5693_, lean_object* v_kind_5694_, lean_object* v_p_5695_, lean_object* v_anonymous_5696_){
_start:
{
uint8_t v_anonymous_boxed_5697_; lean_object* v_res_5698_; 
v_anonymous_boxed_5697_ = lean_unbox(v_anonymous_5696_);
v_res_5698_ = l_Lean_Parser_nodeWithAntiquot(v_name_5693_, v_kind_5694_, v_p_5695_, v_anonymous_boxed_5697_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5703_, lean_object* v_sep_5704_){
_start:
{
lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v_str_5709_; lean_object* v_startInclusive_5710_; lean_object* v_endExclusive_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; 
v___x_5705_ = lean_unsigned_to_nat(0u);
v___x_5706_ = lean_string_utf8_byte_size(v_sep_5704_);
v___x_5707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5707_, 0, v_sep_5704_);
lean_ctor_set(v___x_5707_, 1, v___x_5705_);
lean_ctor_set(v___x_5707_, 2, v___x_5706_);
v___x_5708_ = l_String_Slice_trimAscii(v___x_5707_);
v_str_5709_ = lean_ctor_get(v___x_5708_, 0);
lean_inc_ref(v_str_5709_);
v_startInclusive_5710_ = lean_ctor_get(v___x_5708_, 1);
lean_inc(v_startInclusive_5710_);
v_endExclusive_5711_ = lean_ctor_get(v___x_5708_, 2);
lean_inc(v_endExclusive_5711_);
lean_dec_ref(v___x_5708_);
v___x_5712_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5713_ = lean_string_utf8_extract_fast(v_str_5709_, v_startInclusive_5710_, v_endExclusive_5711_);
lean_dec(v_endExclusive_5711_);
lean_dec(v_startInclusive_5710_);
lean_dec_ref(v_str_5709_);
v___x_5714_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5715_ = lean_string_append(v___x_5713_, v___x_5714_);
v___x_5716_ = l_Lean_Parser_symbol(v___x_5715_);
v___x_5717_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5712_, v_p_5703_, v___x_5716_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5718_, lean_object* v_sep_5719_, lean_object* v_psep_5720_, uint8_t v_allowTrailingSep_5721_){
_start:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; 
v___x_5722_ = l_Lean_Parser_sepByElemParser(v_p_5718_, v_sep_5719_);
v___x_5723_ = l_Lean_Parser_sepByNoAntiquot(v___x_5722_, v_psep_5720_, v_allowTrailingSep_5721_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5724_, lean_object* v_sep_5725_, lean_object* v_psep_5726_, lean_object* v_allowTrailingSep_5727_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5728_; lean_object* v_res_5729_; 
v_allowTrailingSep_boxed_5728_ = lean_unbox(v_allowTrailingSep_5727_);
v_res_5729_ = l_Lean_Parser_sepBy(v_p_5724_, v_sep_5725_, v_psep_5726_, v_allowTrailingSep_boxed_5728_);
return v_res_5729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5730_, lean_object* v_sep_5731_, lean_object* v_psep_5732_, uint8_t v_allowTrailingSep_5733_){
_start:
{
lean_object* v___x_5734_; lean_object* v___x_5735_; 
v___x_5734_ = l_Lean_Parser_sepByElemParser(v_p_5730_, v_sep_5731_);
v___x_5735_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5734_, v_psep_5732_, v_allowTrailingSep_5733_);
return v___x_5735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5736_, lean_object* v_sep_5737_, lean_object* v_psep_5738_, lean_object* v_allowTrailingSep_5739_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5740_; lean_object* v_res_5741_; 
v_allowTrailingSep_boxed_5740_ = lean_unbox(v_allowTrailingSep_5739_);
v_res_5741_ = l_Lean_Parser_sepBy1(v_p_5736_, v_sep_5737_, v_psep_5738_, v_allowTrailingSep_boxed_5740_);
return v_res_5741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5742_, lean_object* v_iniSz_5743_){
_start:
{
lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5744_ = l_Lean_Parser_ParserState_stackSize(v_s_5742_);
v___x_5745_ = lean_unsigned_to_nat(1u);
v___x_5746_ = lean_nat_add(v_iniSz_5743_, v___x_5745_);
v___x_5747_ = lean_nat_dec_eq(v___x_5744_, v___x_5746_);
lean_dec(v___x_5746_);
lean_dec(v___x_5744_);
if (v___x_5747_ == 0)
{
lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5748_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5749_ = l_Lean_Parser_ParserState_mkNode(v_s_5742_, v___x_5748_, v_iniSz_5743_);
return v___x_5749_;
}
else
{
return v_s_5742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5750_, lean_object* v_iniSz_5751_){
_start:
{
lean_object* v_res_5752_; 
v_res_5752_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5750_, v_iniSz_5751_);
lean_dec(v_iniSz_5751_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5753_, lean_object* v_tables_5754_, uint8_t v_behavior_5755_, lean_object* v_c_5756_, lean_object* v_s_5757_){
_start:
{
lean_object* v_leadingTable_5758_; lean_object* v_leadingParsers_5759_; lean_object* v_iniSz_5760_; lean_object* v___x_5761_; lean_object* v_fst_5762_; lean_object* v_snd_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5785_; 
v_leadingTable_5758_ = lean_ctor_get(v_tables_5754_, 0);
lean_inc(v_leadingTable_5758_);
v_leadingParsers_5759_ = lean_ctor_get(v_tables_5754_, 1);
lean_inc(v_leadingParsers_5759_);
lean_dec_ref(v_tables_5754_);
v_iniSz_5760_ = l_Lean_Parser_ParserState_stackSize(v_s_5757_);
lean_inc_ref(v_c_5756_);
v___x_5761_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5758_, v_c_5756_, v_s_5757_, v_behavior_5755_);
lean_dec(v_leadingTable_5758_);
v_fst_5762_ = lean_ctor_get(v___x_5761_, 0);
v_snd_5763_ = lean_ctor_get(v___x_5761_, 1);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5765_ = v___x_5761_;
v_isShared_5766_ = v_isSharedCheck_5785_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_snd_5763_);
lean_inc(v_fst_5762_);
lean_dec(v___x_5761_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5785_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v_errorMsg_5767_; lean_object* v___x_5768_; uint8_t v___x_5769_; 
v_errorMsg_5767_ = lean_ctor_get(v_fst_5762_, 4);
v___x_5768_ = lean_box(0);
v___x_5769_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5767_, v___x_5768_);
if (v___x_5769_ == 0)
{
lean_del_object(v___x_5765_);
lean_dec(v_snd_5763_);
lean_dec(v_iniSz_5760_);
lean_dec(v_leadingParsers_5759_);
lean_dec_ref(v_c_5756_);
lean_dec(v_kind_5753_);
return v_fst_5762_;
}
else
{
lean_object* v_ps_5770_; uint8_t v___x_5771_; 
v_ps_5770_ = l_List_appendTR___redArg(v_leadingParsers_5759_, v_snd_5763_);
v___x_5771_ = l_List_isEmpty___redArg(v_ps_5770_);
if (v___x_5771_ == 0)
{
lean_object* v_s_5772_; lean_object* v___x_5773_; 
lean_del_object(v___x_5765_);
lean_dec(v_kind_5753_);
v_s_5772_ = l_Lean_Parser_longestMatchFn(v___x_5768_, v_ps_5770_, v_c_5756_, v_fst_5762_);
v___x_5773_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5772_, v_iniSz_5760_);
lean_dec(v_iniSz_5760_);
return v___x_5773_;
}
else
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5777_; 
lean_dec(v_ps_5770_);
lean_dec(v_iniSz_5760_);
v___x_5774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5753_, v___x_5771_);
v___x_5775_ = lean_box(0);
lean_inc_ref(v___x_5774_);
if (v_isShared_5766_ == 0)
{
lean_ctor_set_tag(v___x_5765_, 1);
lean_ctor_set(v___x_5765_, 1, v___x_5775_);
lean_ctor_set(v___x_5765_, 0, v___x_5774_);
v___x_5777_ = v___x_5765_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5774_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v___x_5775_);
v___x_5777_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
lean_object* v_s_5778_; lean_object* v_errorMsg_5782_; uint8_t v___x_5783_; 
v_s_5778_ = l_Lean_Parser_tokenFn(v___x_5777_, v_c_5756_, v_fst_5762_);
v_errorMsg_5782_ = lean_ctor_get(v_s_5778_, 4);
v___x_5783_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5782_, v___x_5768_);
if (v___x_5783_ == 0)
{
if (v___x_5771_ == 0)
{
goto v___jp_5779_;
}
else
{
lean_dec_ref(v___x_5774_);
return v_s_5778_;
}
}
else
{
goto v___jp_5779_;
}
v___jp_5779_:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; 
v___x_5780_ = lean_unsigned_to_nat(0u);
v___x_5781_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5778_, v___x_5774_, v___x_5780_);
return v___x_5781_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5786_, lean_object* v_tables_5787_, lean_object* v_behavior_5788_, lean_object* v_c_5789_, lean_object* v_s_5790_){
_start:
{
uint8_t v_behavior_boxed_5791_; lean_object* v_res_5792_; 
v_behavior_boxed_5791_ = lean_unbox(v_behavior_5788_);
v_res_5792_ = l_Lean_Parser_leadingParserAux(v_kind_5786_, v_tables_5787_, v_behavior_boxed_5791_, v_c_5789_, v_s_5790_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5793_, lean_object* v_tables_5794_, uint8_t v_behavior_5795_, lean_object* v_antiquotParser_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_){
_start:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; uint8_t v___x_5801_; lean_object* v___x_5802_; 
v___x_5799_ = lean_box(v_behavior_5795_);
v___x_5800_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5800_, 0, v_kind_5793_);
lean_closure_set(v___x_5800_, 1, v_tables_5794_);
lean_closure_set(v___x_5800_, 2, v___x_5799_);
v___x_5801_ = 0;
v___x_5802_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5796_, v___x_5800_, v___x_5801_, v_a_5797_, v_a_5798_);
return v___x_5802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5803_, lean_object* v_tables_5804_, lean_object* v_behavior_5805_, lean_object* v_antiquotParser_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_){
_start:
{
uint8_t v_behavior_boxed_5809_; lean_object* v_res_5810_; 
v_behavior_boxed_5809_ = lean_unbox(v_behavior_5805_);
v_res_5810_ = l_Lean_Parser_leadingParser(v_kind_5803_, v_tables_5804_, v_behavior_boxed_5809_, v_antiquotParser_5806_, v_a_5807_, v_a_5808_);
return v_res_5810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5811_, lean_object* v_left_5812_, lean_object* v_ps_5813_, lean_object* v_c_5814_, lean_object* v_s_5815_){
_start:
{
lean_object* v_trailingParsers_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; 
v_trailingParsers_5816_ = lean_ctor_get(v_tables_5811_, 3);
lean_inc(v_trailingParsers_5816_);
lean_dec_ref(v_tables_5811_);
v___x_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5817_, 0, v_left_5812_);
v___x_5818_ = l_List_appendTR___redArg(v_ps_5813_, v_trailingParsers_5816_);
v___x_5819_ = l_Lean_Parser_longestMatchFn(v___x_5817_, v___x_5818_, v_c_5814_, v_s_5815_);
return v___x_5819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5820_, lean_object* v_c_5821_, lean_object* v_s_5822_){
_start:
{
lean_object* v_pos_5823_; lean_object* v_trailingTable_5824_; lean_object* v_trailingParsers_5825_; lean_object* v_iniSz_5826_; uint8_t v___x_5827_; lean_object* v___x_5828_; lean_object* v_fst_5829_; lean_object* v_snd_5830_; lean_object* v_stxStack_5831_; lean_object* v_errorMsg_5832_; lean_object* v___x_5847_; uint8_t v___x_5848_; 
v_pos_5823_ = lean_ctor_get(v_s_5822_, 2);
lean_inc(v_pos_5823_);
v_trailingTable_5824_ = lean_ctor_get(v_tables_5820_, 2);
v_trailingParsers_5825_ = lean_ctor_get(v_tables_5820_, 3);
v_iniSz_5826_ = l_Lean_Parser_ParserState_stackSize(v_s_5822_);
v___x_5827_ = 0;
lean_inc_ref(v_c_5821_);
v___x_5828_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5824_, v_c_5821_, v_s_5822_, v___x_5827_);
v_fst_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_fst_5829_);
v_snd_5830_ = lean_ctor_get(v___x_5828_, 1);
lean_inc(v_snd_5830_);
lean_dec_ref(v___x_5828_);
v_stxStack_5831_ = lean_ctor_get(v_fst_5829_, 0);
v_errorMsg_5832_ = lean_ctor_get(v_fst_5829_, 4);
v___x_5847_ = lean_box(0);
v___x_5848_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5832_, v___x_5847_);
if (v___x_5848_ == 0)
{
lean_object* v___x_5849_; 
lean_dec(v_snd_5830_);
lean_dec_ref(v_c_5821_);
lean_dec_ref(v_tables_5820_);
v___x_5849_ = l_Lean_Parser_ParserState_restore(v_fst_5829_, v_iniSz_5826_, v_pos_5823_);
lean_dec(v_iniSz_5826_);
return v___x_5849_;
}
else
{
uint8_t v___x_5850_; 
v___x_5850_ = l_List_isEmpty___redArg(v_snd_5830_);
if (v___x_5850_ == 0)
{
goto v___jp_5833_;
}
else
{
uint8_t v___x_5851_; 
v___x_5851_ = l_List_isEmpty___redArg(v_trailingParsers_5825_);
if (v___x_5851_ == 0)
{
goto v___jp_5833_;
}
else
{
lean_dec(v_snd_5830_);
lean_dec(v_iniSz_5826_);
lean_dec(v_pos_5823_);
lean_dec_ref(v_c_5821_);
lean_dec_ref(v_tables_5820_);
return v_fst_5829_;
}
}
}
v___jp_5833_:
{
lean_object* v_left_5834_; lean_object* v_s_5835_; lean_object* v_s_5836_; lean_object* v_pos_5837_; lean_object* v_errorMsg_5838_; lean_object* v___x_5839_; uint8_t v___x_5840_; 
v_left_5834_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5831_);
v_s_5835_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5829_);
lean_inc_ref(v_c_5821_);
lean_inc(v_left_5834_);
lean_inc_ref(v_tables_5820_);
v_s_5836_ = l_Lean_Parser_trailingLoopStep(v_tables_5820_, v_left_5834_, v_snd_5830_, v_c_5821_, v_s_5835_);
v_pos_5837_ = lean_ctor_get(v_s_5836_, 2);
v_errorMsg_5838_ = lean_ctor_get(v_s_5836_, 4);
v___x_5839_ = lean_box(0);
v___x_5840_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5838_, v___x_5839_);
if (v___x_5840_ == 0)
{
uint8_t v_decide_5841_; 
lean_dec_ref(v_c_5821_);
lean_dec_ref(v_tables_5820_);
v_decide_5841_ = lean_nat_dec_eq(v_pos_5837_, v_pos_5823_);
if (v_decide_5841_ == 0)
{
lean_dec(v_left_5834_);
lean_dec(v_iniSz_5826_);
lean_dec(v_pos_5823_);
return v_s_5836_;
}
else
{
lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5842_ = lean_unsigned_to_nat(1u);
v___x_5843_ = lean_nat_sub(v_iniSz_5826_, v___x_5842_);
lean_dec(v_iniSz_5826_);
v___x_5844_ = l_Lean_Parser_ParserState_restore(v_s_5836_, v___x_5843_, v_pos_5823_);
lean_dec(v___x_5843_);
v___x_5845_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5844_, v_left_5834_);
return v___x_5845_;
}
}
else
{
lean_dec(v_left_5834_);
lean_dec(v_iniSz_5826_);
lean_dec(v_pos_5823_);
v_s_5822_ = v_s_5836_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5852_, lean_object* v_tables_5853_, uint8_t v_behavior_5854_, lean_object* v_antiquotParser_5855_, lean_object* v_c_5856_, lean_object* v_s_5857_){
_start:
{
lean_object* v_s_5858_; lean_object* v_errorMsg_5859_; lean_object* v___x_5860_; uint8_t v___x_5861_; 
lean_inc_ref(v_c_5856_);
lean_inc_ref(v_tables_5853_);
v_s_5858_ = l_Lean_Parser_leadingParser(v_kind_5852_, v_tables_5853_, v_behavior_5854_, v_antiquotParser_5855_, v_c_5856_, v_s_5857_);
v_errorMsg_5859_ = lean_ctor_get(v_s_5858_, 4);
v___x_5860_ = lean_box(0);
v___x_5861_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5859_, v___x_5860_);
if (v___x_5861_ == 0)
{
lean_dec_ref(v_c_5856_);
lean_dec_ref(v_tables_5853_);
return v_s_5858_;
}
else
{
lean_object* v___x_5862_; 
v___x_5862_ = l_Lean_Parser_trailingLoop(v_tables_5853_, v_c_5856_, v_s_5858_);
return v___x_5862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5863_, lean_object* v_tables_5864_, lean_object* v_behavior_5865_, lean_object* v_antiquotParser_5866_, lean_object* v_c_5867_, lean_object* v_s_5868_){
_start:
{
uint8_t v_behavior_boxed_5869_; lean_object* v_res_5870_; 
v_behavior_boxed_5869_ = lean_unbox(v_behavior_5865_);
v_res_5870_ = l_Lean_Parser_prattParser(v_kind_5863_, v_tables_5864_, v_behavior_boxed_5869_, v_antiquotParser_5866_, v_c_5867_, v_s_5868_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5875_, lean_object* v_s_5876_){
_start:
{
lean_object* v_toInputContext_5877_; lean_object* v_pos_5878_; lean_object* v_inputString_5879_; lean_object* v_initStackSz_5880_; uint32_t v_curr_5885_; uint32_t v___x_5886_; uint8_t v___x_5887_; 
v_toInputContext_5877_ = lean_ctor_get(v_c_5875_, 0);
v_pos_5878_ = lean_ctor_get(v_s_5876_, 2);
lean_inc(v_pos_5878_);
v_inputString_5879_ = lean_ctor_get(v_toInputContext_5877_, 0);
v_initStackSz_5880_ = l_Lean_Parser_ParserState_stackSize(v_s_5876_);
v_curr_5885_ = lean_string_utf8_get(v_inputString_5879_, v_pos_5878_);
v___x_5886_ = 48;
v___x_5887_ = lean_uint32_dec_le(v___x_5886_, v_curr_5885_);
if (v___x_5887_ == 0)
{
lean_dec_ref(v_c_5875_);
goto v___jp_5881_;
}
else
{
uint32_t v___x_5888_; uint8_t v___x_5889_; 
v___x_5888_ = 57;
v___x_5889_ = lean_uint32_dec_le(v_curr_5885_, v___x_5888_);
if (v___x_5889_ == 0)
{
lean_dec_ref(v_c_5875_);
goto v___jp_5881_;
}
else
{
uint8_t v___x_5890_; 
v___x_5890_ = lean_uint32_dec_eq(v_curr_5885_, v___x_5886_);
if (v___x_5890_ == 0)
{
lean_object* v___f_5891_; lean_object* v_s_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; 
lean_dec(v_initStackSz_5880_);
v___f_5891_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_s_5892_ = l_Lean_Parser_takeWhileFn(v___f_5891_, v_c_5875_, v_s_5876_);
v___x_5893_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5894_ = l_Lean_Parser_mkNodeToken(v___x_5893_, v_pos_5878_, v___x_5889_, v_c_5875_, v_s_5892_);
return v___x_5894_;
}
else
{
lean_dec_ref(v_c_5875_);
goto v___jp_5881_;
}
}
}
v___jp_5881_:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5882_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5883_, 0, v_initStackSz_5880_);
v___x_5884_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5876_, v___x_5882_, v_pos_5878_, v___x_5883_);
lean_dec_ref_known(v___x_5883_, 1);
return v___x_5884_;
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5895_; uint8_t v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5895_ = 0;
v___x_5896_ = 1;
v___x_5897_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5898_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5899_ = l_Lean_Parser_mkAntiquot(v___x_5898_, v___x_5897_, v___x_5896_, v___x_5895_);
return v___x_5899_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; 
v___x_5900_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5901_ = l_Lean_Parser_mkAtomicInfo(v___x_5900_);
return v___x_5901_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5902_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5903_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5903_);
lean_ctor_set(v___x_5904_, 1, v___x_5902_);
return v___x_5904_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5905_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5906_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5907_ = l_Lean_Parser_withAntiquot(v___x_5906_, v___x_5905_);
return v___x_5907_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5908_; 
v___x_5908_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5909_, lean_object* v_s_5910_){
_start:
{
lean_inc_ref(v_s_5910_);
return v_s_5910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5911_, lean_object* v_s_5912_){
_start:
{
lean_object* v_res_5913_; 
v_res_5913_ = l_Lean_Parser_skip___lam__0(v_x_5911_, v_s_5912_);
lean_dec_ref(v_s_5912_);
lean_dec_ref(v_x_5911_);
return v_res_5913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5919_, lean_object* v_s_5920_, lean_object* v_f_5921_, lean_object* v_b_5922_){
_start:
{
lean_object* v_toApplicative_5923_; lean_object* v_toPure_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; uint8_t v___x_5928_; 
v_toApplicative_5923_ = lean_ctor_get(v_inst_5919_, 0);
v_toPure_5924_ = lean_ctor_get(v_toApplicative_5923_, 1);
v___x_5925_ = l_Lean_Syntax_getArgs(v_s_5920_);
v___x_5926_ = lean_unsigned_to_nat(0u);
v___x_5927_ = lean_array_get_size(v___x_5925_);
v___x_5928_ = lean_nat_dec_lt(v___x_5926_, v___x_5927_);
if (v___x_5928_ == 0)
{
lean_object* v___x_5929_; 
lean_inc(v_toPure_5924_);
lean_dec_ref(v___x_5925_);
lean_dec(v_f_5921_);
lean_dec_ref(v_inst_5919_);
v___x_5929_ = lean_apply_2(v_toPure_5924_, lean_box(0), v_b_5922_);
return v___x_5929_;
}
else
{
lean_object* v___x_5930_; uint8_t v___x_5931_; 
v___x_5930_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5930_, 0, lean_box(0));
lean_closure_set(v___x_5930_, 1, lean_box(0));
lean_closure_set(v___x_5930_, 2, lean_box(0));
lean_closure_set(v___x_5930_, 3, v_f_5921_);
v___x_5931_ = lean_nat_dec_le(v___x_5927_, v___x_5927_);
if (v___x_5931_ == 0)
{
if (v___x_5928_ == 0)
{
lean_object* v___x_5932_; 
lean_inc(v_toPure_5924_);
lean_dec_ref(v___x_5930_);
lean_dec_ref(v___x_5925_);
lean_dec_ref(v_inst_5919_);
v___x_5932_ = lean_apply_2(v_toPure_5924_, lean_box(0), v_b_5922_);
return v___x_5932_;
}
else
{
size_t v___x_5933_; size_t v___x_5934_; lean_object* v___x_5935_; 
v___x_5933_ = ((size_t)0ULL);
v___x_5934_ = lean_usize_of_nat(v___x_5927_);
v___x_5935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5919_, v___x_5930_, v___x_5925_, v___x_5933_, v___x_5934_, v_b_5922_);
return v___x_5935_;
}
}
else
{
size_t v___x_5936_; size_t v___x_5937_; lean_object* v___x_5938_; 
v___x_5936_ = ((size_t)0ULL);
v___x_5937_ = lean_usize_of_nat(v___x_5927_);
v___x_5938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5919_, v___x_5930_, v___x_5925_, v___x_5936_, v___x_5937_, v_b_5922_);
return v___x_5938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5939_, lean_object* v_s_5940_, lean_object* v_f_5941_, lean_object* v_b_5942_){
_start:
{
lean_object* v_res_5943_; 
v_res_5943_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5939_, v_s_5940_, v_f_5941_, v_b_5942_);
lean_dec(v_s_5940_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5944_, lean_object* v_inst_5945_, lean_object* v_00_u03b2_5946_, lean_object* v_s_5947_, lean_object* v_f_5948_, lean_object* v_b_5949_){
_start:
{
lean_object* v___x_5950_; 
v___x_5950_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5945_, v_s_5947_, v_f_5948_, v_b_5949_);
return v___x_5950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5951_, lean_object* v_inst_5952_, lean_object* v_00_u03b2_5953_, lean_object* v_s_5954_, lean_object* v_f_5955_, lean_object* v_b_5956_){
_start:
{
lean_object* v_res_5957_; 
v_res_5957_ = l_Lean_Syntax_foldArgsM(v_m_5951_, v_inst_5952_, v_00_u03b2_5953_, v_s_5954_, v_f_5955_, v_b_5956_);
lean_dec(v_s_5954_);
return v_res_5957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5958_, lean_object* v_x1_5959_, lean_object* v_x2_5960_){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = lean_apply_2(v_f_5958_, v_x1_5959_, v_x2_5960_);
return v___x_5961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5962_, lean_object* v_as_5963_, size_t v_i_5964_, size_t v_stop_5965_, lean_object* v_b_5966_){
_start:
{
uint8_t v___x_5967_; 
v___x_5967_ = lean_usize_dec_eq(v_i_5964_, v_stop_5965_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5968_; lean_object* v___x_5969_; size_t v___x_5970_; size_t v___x_5971_; 
v___x_5968_ = lean_array_uget_borrowed(v_as_5963_, v_i_5964_);
lean_inc(v_f_5962_);
lean_inc(v___x_5968_);
v___x_5969_ = lean_apply_2(v_f_5962_, v___x_5968_, v_b_5966_);
v___x_5970_ = ((size_t)1ULL);
v___x_5971_ = lean_usize_add(v_i_5964_, v___x_5970_);
v_i_5964_ = v___x_5971_;
v_b_5966_ = v___x_5969_;
goto _start;
}
else
{
lean_dec(v_f_5962_);
return v_b_5966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5973_, lean_object* v_as_5974_, lean_object* v_i_5975_, lean_object* v_stop_5976_, lean_object* v_b_5977_){
_start:
{
size_t v_i_boxed_5978_; size_t v_stop_boxed_5979_; lean_object* v_res_5980_; 
v_i_boxed_5978_ = lean_unbox_usize(v_i_5975_);
lean_dec(v_i_5975_);
v_stop_boxed_5979_ = lean_unbox_usize(v_stop_5976_);
lean_dec(v_stop_5976_);
v_res_5980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5973_, v_as_5974_, v_i_boxed_5978_, v_stop_boxed_5979_, v_b_5977_);
lean_dec_ref(v_as_5974_);
return v_res_5980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5981_, lean_object* v_f_5982_, lean_object* v_b_5983_){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; uint8_t v___x_5987_; 
v___x_5984_ = l_Lean_Syntax_getArgs(v_s_5981_);
v___x_5985_ = lean_unsigned_to_nat(0u);
v___x_5986_ = lean_array_get_size(v___x_5984_);
v___x_5987_ = lean_nat_dec_lt(v___x_5985_, v___x_5986_);
if (v___x_5987_ == 0)
{
lean_dec_ref(v___x_5984_);
lean_dec(v_f_5982_);
return v_b_5983_;
}
else
{
size_t v___x_5988_; size_t v___x_5989_; lean_object* v___x_5990_; 
v___x_5988_ = ((size_t)0ULL);
v___x_5989_ = lean_usize_of_nat(v___x_5986_);
v___x_5990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5982_, v___x_5984_, v___x_5988_, v___x_5989_, v_b_5983_);
lean_dec_ref(v___x_5984_);
return v___x_5990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5991_, lean_object* v_f_5992_, lean_object* v_b_5993_){
_start:
{
lean_object* v_res_5994_; 
v_res_5994_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5991_, v_f_5992_, v_b_5993_);
lean_dec(v_s_5991_);
return v_res_5994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5995_, lean_object* v_f_5996_, lean_object* v_b_5997_){
_start:
{
lean_object* v___f_5998_; lean_object* v___x_5999_; 
v___f_5998_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5998_, 0, v_f_5996_);
v___x_5999_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5995_, v___f_5998_, v_b_5997_);
return v___x_5999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_6000_, lean_object* v_f_6001_, lean_object* v_b_6002_){
_start:
{
lean_object* v_res_6003_; 
v_res_6003_ = l_Lean_Syntax_foldArgs___redArg(v_s_6000_, v_f_6001_, v_b_6002_);
lean_dec(v_s_6000_);
return v_res_6003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_6004_, lean_object* v_s_6005_, lean_object* v_f_6006_, lean_object* v_b_6007_){
_start:
{
lean_object* v___x_6008_; 
v___x_6008_ = l_Lean_Syntax_foldArgs___redArg(v_s_6005_, v_f_6006_, v_b_6007_);
return v___x_6008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_6009_, lean_object* v_s_6010_, lean_object* v_f_6011_, lean_object* v_b_6012_){
_start:
{
lean_object* v_res_6013_; 
v_res_6013_ = l_Lean_Syntax_foldArgs(v_00_u03b2_6009_, v_s_6010_, v_f_6011_, v_b_6012_);
lean_dec(v_s_6010_);
return v_res_6013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_6014_, lean_object* v_s_6015_, lean_object* v_f_6016_, lean_object* v_b_6017_){
_start:
{
lean_object* v___x_6018_; 
v___x_6018_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_6015_, v_f_6016_, v_b_6017_);
return v___x_6018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_6019_, lean_object* v_s_6020_, lean_object* v_f_6021_, lean_object* v_b_6022_){
_start:
{
lean_object* v_res_6023_; 
v_res_6023_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_6019_, v_s_6020_, v_f_6021_, v_b_6022_);
lean_dec(v_s_6020_);
return v_res_6023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_6024_, lean_object* v_f_6025_, lean_object* v_as_6026_, size_t v_i_6027_, size_t v_stop_6028_, lean_object* v_b_6029_){
_start:
{
lean_object* v___x_6030_; 
v___x_6030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_6025_, v_as_6026_, v_i_6027_, v_stop_6028_, v_b_6029_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_6031_, lean_object* v_f_6032_, lean_object* v_as_6033_, lean_object* v_i_6034_, lean_object* v_stop_6035_, lean_object* v_b_6036_){
_start:
{
size_t v_i_boxed_6037_; size_t v_stop_boxed_6038_; lean_object* v_res_6039_; 
v_i_boxed_6037_ = lean_unbox_usize(v_i_6034_);
lean_dec(v_i_6034_);
v_stop_boxed_6038_ = lean_unbox_usize(v_stop_6035_);
lean_dec(v_stop_6035_);
v_res_6039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_6031_, v_f_6032_, v_as_6033_, v_i_boxed_6037_, v_stop_boxed_6038_, v_b_6036_);
lean_dec_ref(v_as_6033_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_6040_, lean_object* v_s_6041_, lean_object* v_x_6042_){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = lean_apply_1(v_f_6040_, v_s_6041_);
return v___x_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_6044_, lean_object* v_s_6045_, lean_object* v_f_6046_){
_start:
{
lean_object* v___f_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___f_6047_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6047_, 0, v_f_6046_);
v___x_6048_ = lean_box(0);
v___x_6049_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6044_, v_s_6045_, v___f_6047_, v___x_6048_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_6050_, lean_object* v_s_6051_, lean_object* v_f_6052_){
_start:
{
lean_object* v_res_6053_; 
v_res_6053_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6050_, v_s_6051_, v_f_6052_);
lean_dec(v_s_6051_);
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_6054_, lean_object* v_inst_6055_, lean_object* v_s_6056_, lean_object* v_f_6057_){
_start:
{
lean_object* v___x_6058_; 
v___x_6058_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6055_, v_s_6056_, v_f_6057_);
return v___x_6058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_6059_, lean_object* v_inst_6060_, lean_object* v_s_6061_, lean_object* v_f_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l_Lean_Syntax_forArgsM(v_m_6059_, v_inst_6060_, v_s_6061_, v_f_6062_);
lean_dec(v_s_6061_);
return v_res_6063_;
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
res = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1();
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
