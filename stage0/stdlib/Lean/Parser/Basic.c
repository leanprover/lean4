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
uint8_t l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(lean_object* v_x_145_, lean_object* v_x_146_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_145_ = stack[0].m_obj;
lean_object* v_x_146_ = stack[1].m_obj;
uint8_t v_res_153_;
v_res_153_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_x_145_, v_x_146_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_x_154_, v_x_155_);
lean_dec(v_x_155_);
lean_dec(v_x_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object* v_p_158_, lean_object* v_q_159_, lean_object* v_c_160_, lean_object* v_s_161_){
_start:
{
lean_object* v_s_162_; lean_object* v_errorMsg_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
lean_inc_ref(v_c_160_);
v_s_162_ = lean_apply_2(v_p_158_, v_c_160_, v_s_161_);
v_errorMsg_163_ = lean_ctor_get(v_s_162_, 4);
lean_inc(v_errorMsg_163_);
v___x_164_ = lean_box(0);
v___x_165_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_163_, v___x_164_);
lean_dec(v_errorMsg_163_);
if (v___x_165_ == 0)
{
lean_dec_ref(v_c_160_);
lean_dec_ref(v_q_159_);
return v_s_162_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_apply_2(v_q_159_, v_c_160_, v_s_162_);
return v___x_166_;
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
lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* v_msg_288_, uint8_t v_delta_289_, lean_object* v_c_290_, lean_object* v_s_291_){
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
LEAN_EXPORT void l_Lean_Parser_errorAtSavedPosFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_288_ = stack[0].m_obj;
uint8_t v_delta_289_ = stack[1].m_num;
lean_object* v_c_290_ = stack[2].m_obj;
lean_object* v_s_291_ = stack[3].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Lean_Parser_errorAtSavedPosFn(v_msg_288_, v_delta_289_, v_c_290_, v_s_291_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object* v_msg_302_, lean_object* v_delta_303_, lean_object* v_c_304_, lean_object* v_s_305_){
_start:
{
uint8_t v_delta_boxed_306_; lean_object* v_res_307_; 
v_delta_boxed_306_ = lean_unbox(v_delta_303_);
v_res_307_ = l_Lean_Parser_errorAtSavedPosFn(v_msg_302_, v_delta_boxed_306_, v_c_304_, v_s_305_);
return v_res_307_;
}
}
lean_object* l_Lean_Parser_errorAtSavedPos(lean_object* v_msg_312_, uint8_t v_delta_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_315_ = lean_box(v_delta_313_);
v___x_316_ = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn___boxed), 4, 2);
lean_closure_set(v___x_316_, 0, v_msg_312_);
lean_closure_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Lean_Parser_errorAtSavedPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_312_ = stack[0].m_obj;
uint8_t v_delta_313_ = stack[1].m_num;
lean_object* v_res_318_;
v_res_318_ = l_Lean_Parser_errorAtSavedPos(v_msg_312_, v_delta_313_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object* v_msg_319_, lean_object* v_delta_320_){
_start:
{
uint8_t v_delta_boxed_321_; lean_object* v_res_322_; 
v_delta_boxed_321_ = lean_unbox(v_delta_320_);
v_res_322_ = l_Lean_Parser_errorAtSavedPos(v_msg_319_, v_delta_boxed_321_);
return v_res_322_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3));
v___x_333_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4));
v___x_334_ = l_Lean_addBuiltinDocString(v___x_332_, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_335_;
v_res_335_ = l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Parser_Basic_0__Lean_Parser_errorAtSavedPos___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object* v_prec_339_, lean_object* v_c_340_, lean_object* v_s_341_){
_start:
{
lean_object* v_toCacheableParserContext_342_; lean_object* v_prec_343_; uint8_t v___x_344_; 
v_toCacheableParserContext_342_ = lean_ctor_get(v_c_340_, 2);
v_prec_343_ = lean_ctor_get(v_toCacheableParserContext_342_, 0);
v___x_344_ = lean_nat_dec_le(v_prec_343_, v_prec_339_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; 
v___x_345_ = ((lean_object*)(l_Lean_Parser_checkPrecFn___closed__0));
v___x_346_ = lean_box(0);
v___x_347_ = 1;
v___x_348_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_341_, v___x_345_, v___x_346_, v___x_347_);
return v___x_348_;
}
else
{
return v_s_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object* v_prec_349_, lean_object* v_c_350_, lean_object* v_s_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Parser_checkPrecFn(v_prec_349_, v_c_350_, v_s_351_);
lean_dec_ref(v_c_350_);
lean_dec(v_prec_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object* v_prec_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_355_ = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(v___x_355_, 0, v_prec_353_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg(lean_object* v_prec_357_, lean_object* v_s_358_){
_start:
{
lean_object* v_lhsPrec_359_; uint8_t v___x_360_; 
v_lhsPrec_359_ = lean_ctor_get(v_s_358_, 1);
v___x_360_ = lean_nat_dec_le(v_prec_357_, v_lhsPrec_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v___x_361_ = ((lean_object*)(l_Lean_Parser_checkPrecFn___closed__0));
v___x_362_ = lean_box(0);
v___x_363_ = 1;
v___x_364_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_358_, v___x_361_, v___x_362_, v___x_363_);
return v___x_364_;
}
else
{
return v_s_358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg___boxed(lean_object* v_prec_365_, lean_object* v_s_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Parser_checkLhsPrecFn___redArg(v_prec_365_, v_s_366_);
lean_dec(v_prec_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object* v_prec_368_, lean_object* v_x_369_, lean_object* v_s_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Parser_checkLhsPrecFn___redArg(v_prec_368_, v_s_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object* v_prec_372_, lean_object* v_x_373_, lean_object* v_s_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Parser_checkLhsPrecFn(v_prec_372_, v_x_373_, v_s_374_);
lean_dec_ref(v_x_373_);
lean_dec(v_prec_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object* v_prec_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_378_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(v___x_378_, 0, v_prec_376_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___redArg(lean_object* v_prec_380_, lean_object* v_s_381_){
_start:
{
lean_object* v_stxStack_382_; lean_object* v_pos_383_; lean_object* v_cache_384_; lean_object* v_errorMsg_385_; lean_object* v_recoveredErrors_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_stxStack_382_ = lean_ctor_get(v_s_381_, 0);
v_pos_383_ = lean_ctor_get(v_s_381_, 2);
v_cache_384_ = lean_ctor_get(v_s_381_, 3);
v_errorMsg_385_ = lean_ctor_get(v_s_381_, 4);
v_recoveredErrors_386_ = lean_ctor_get(v_s_381_, 5);
v___x_387_ = lean_box(0);
v___x_388_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_385_, v___x_387_);
if (v___x_388_ == 0)
{
lean_dec(v_prec_380_);
return v_s_381_;
}
else
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_inc_ref(v_recoveredErrors_386_);
lean_inc(v_errorMsg_385_);
lean_inc_ref(v_cache_384_);
lean_inc(v_pos_383_);
lean_inc_ref(v_stxStack_382_);
v_isSharedCheck_395_ = !lean_is_exclusive(v_s_381_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_396_ = lean_ctor_get(v_s_381_, 5);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_s_381_, 4);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_s_381_, 3);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_s_381_, 2);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_s_381_, 1);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_s_381_, 0);
lean_dec(v_unused_401_);
v___x_390_ = v_s_381_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_s_381_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_prec_380_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_stxStack_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_prec_380_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_pos_383_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_cache_384_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_errorMsg_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 5, v_recoveredErrors_386_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object* v_prec_402_, lean_object* v_x_403_, lean_object* v_s_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Parser_setLhsPrecFn___redArg(v_prec_402_, v_s_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object* v_prec_406_, lean_object* v_x_407_, lean_object* v_s_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Parser_setLhsPrecFn(v_prec_406_, v_x_407_, v_s_408_);
lean_dec_ref(v_x_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object* v_prec_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_412_ = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(v___x_412_, 0, v_prec_410_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_spec__0(lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_nat_to_int(v_a_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(lean_object* v_i_416_, lean_object* v_c_417_){
_start:
{
lean_object* v_prec_418_; lean_object* v_quotDepth_419_; uint8_t v_suppressInsideQuot_420_; lean_object* v_savedPos_x3f_421_; lean_object* v_forbiddenTks_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_prec_418_ = lean_ctor_get(v_c_417_, 0);
v_quotDepth_419_ = lean_ctor_get(v_c_417_, 1);
v_suppressInsideQuot_420_ = lean_ctor_get_uint8(v_c_417_, sizeof(void*)*4);
v_savedPos_x3f_421_ = lean_ctor_get(v_c_417_, 2);
v_forbiddenTks_422_ = lean_ctor_get(v_c_417_, 3);
v_isSharedCheck_432_ = !lean_is_exclusive(v_c_417_);
if (v_isSharedCheck_432_ == 0)
{
v___x_424_ = v_c_417_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_forbiddenTks_422_);
lean_inc(v_savedPos_x3f_421_);
lean_inc(v_quotDepth_419_);
lean_inc(v_prec_418_);
lean_dec(v_c_417_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_426_ = lean_nat_to_int(v_quotDepth_419_);
v___x_427_ = lean_int_add(v___x_426_, v_i_416_);
lean_dec(v___x_426_);
v___x_428_ = l_Int_toNat(v___x_427_);
lean_dec(v___x_427_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_428_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_prec_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_savedPos_x3f_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_forbiddenTks_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*4, v_suppressInsideQuot_420_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed(lean_object* v_i_433_, lean_object* v_c_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(v_i_433_, v_c_434_);
lean_dec(v_i_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object* v_i_436_, lean_object* v_p_437_){
_start:
{
lean_object* v___f_438_; lean_object* v___x_439_; 
v___f_438_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed), 2, 1);
lean_closure_set(v___f_438_, 0, v_i_436_);
v___x_439_ = l_Lean_Parser_adaptCacheableContext(v___f_438_, v_p_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Parser_incQuotDepth___closed__0(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_to_int(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object* v_p_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___x_444_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(v___x_443_, v_p_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Parser_decQuotDepth___closed__0(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___x_446_ = lean_int_neg(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object* v_p_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_Parser_decQuotDepth___closed__0, &l_Lean_Parser_decQuotDepth___closed__0_once, _init_l_Lean_Parser_decQuotDepth___closed__0);
v___x_449_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(v___x_448_, v_p_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0(lean_object* v_c_450_){
_start:
{
lean_object* v_prec_451_; lean_object* v_quotDepth_452_; lean_object* v_savedPos_x3f_453_; lean_object* v_forbiddenTks_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_prec_451_ = lean_ctor_get(v_c_450_, 0);
v_quotDepth_452_ = lean_ctor_get(v_c_450_, 1);
v_savedPos_x3f_453_ = lean_ctor_get(v_c_450_, 2);
v_forbiddenTks_454_ = lean_ctor_get(v_c_450_, 3);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_nat_dec_eq(v_quotDepth_452_, v___x_455_);
if (v___x_456_ == 0)
{
return v_c_450_;
}
else
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_inc_ref(v_forbiddenTks_454_);
lean_inc(v_savedPos_x3f_453_);
lean_inc(v_quotDepth_452_);
lean_inc(v_prec_451_);
v_isSharedCheck_463_ = !lean_is_exclusive(v_c_450_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_464_ = lean_ctor_get(v_c_450_, 3);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_c_450_, 2);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_c_450_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_c_450_, 0);
lean_dec(v_unused_467_);
v___x_458_ = v_c_450_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_dec(v_c_450_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_prec_451_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_quotDepth_452_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_savedPos_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_forbiddenTks_454_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*4, v___x_456_);
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* v_a_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; 
v___f_470_ = ((lean_object*)(l_Lean_Parser_suppressInsideQuot___closed__0));
v___x_471_ = l_Lean_Parser_adaptCacheableContext(v___f_470_, v_a_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object* v_n_472_, lean_object* v_prec_473_, lean_object* v_p_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_inc(v_prec_473_);
v___x_475_ = l_Lean_Parser_checkPrec(v_prec_473_);
v___x_476_ = l_Lean_Parser_node(v_n_472_, v_p_474_);
v___x_477_ = l_Lean_Parser_setLhsPrec(v_prec_473_);
v___x_478_ = l_Lean_Parser_andthen(v___x_476_, v___x_477_);
v___x_479_ = l_Lean_Parser_andthen(v___x_475_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object* v_n_480_, lean_object* v_p_481_){
_start:
{
lean_object* v_info_482_; lean_object* v_fn_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_492_; 
v_info_482_ = lean_ctor_get(v_p_481_, 0);
v_fn_483_ = lean_ctor_get(v_p_481_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_p_481_);
if (v_isSharedCheck_492_ == 0)
{
v___x_485_ = v_p_481_;
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_fn_483_);
lean_inc(v_info_482_);
lean_dec(v_p_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
lean_inc(v_n_480_);
v___x_487_ = l_Lean_Parser_nodeInfo(v_n_480_, v_info_482_);
v___x_488_ = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(v___x_488_, 0, v_n_480_);
lean_closure_set(v___x_488_, 1, v_fn_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_488_);
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object* v_n_493_, lean_object* v_prec_494_, lean_object* v_lhsPrec_495_, lean_object* v_p_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_inc(v_prec_494_);
v___x_497_ = l_Lean_Parser_checkPrec(v_prec_494_);
v___x_498_ = l_Lean_Parser_checkLhsPrec(v_lhsPrec_495_);
v___x_499_ = l_Lean_Parser_trailingNodeAux(v_n_493_, v_p_496_);
v___x_500_ = l_Lean_Parser_setLhsPrec(v_prec_494_);
v___x_501_ = l_Lean_Parser_andthen(v___x_499_, v___x_500_);
v___x_502_ = l_Lean_Parser_andthen(v___x_498_, v___x_501_);
v___x_503_ = l_Lean_Parser_andthen(v___x_497_, v___x_502_);
return v___x_503_;
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* v_s_504_, lean_object* v_error1_505_, lean_object* v_iniPos_506_, uint8_t v_mergeErrors_507_){
_start:
{
lean_object* v_stxStack_508_; lean_object* v_lhsPrec_509_; lean_object* v_pos_510_; lean_object* v_cache_511_; lean_object* v_errorMsg_512_; lean_object* v_recoveredErrors_513_; lean_object* v___y_515_; 
v_stxStack_508_ = lean_ctor_get(v_s_504_, 0);
v_lhsPrec_509_ = lean_ctor_get(v_s_504_, 1);
v_pos_510_ = lean_ctor_get(v_s_504_, 2);
v_cache_511_ = lean_ctor_get(v_s_504_, 3);
v_errorMsg_512_ = lean_ctor_get(v_s_504_, 4);
v_recoveredErrors_513_ = lean_ctor_get(v_s_504_, 5);
if (lean_obj_tag(v_errorMsg_512_) == 1)
{
lean_object* v_val_518_; uint8_t v_decide_519_; 
v_val_518_ = lean_ctor_get(v_errorMsg_512_, 0);
v_decide_519_ = lean_nat_dec_eq(v_pos_510_, v_iniPos_506_);
if (v_decide_519_ == 0)
{
lean_dec_ref(v_error1_505_);
return v_s_504_;
}
else
{
lean_inc(v_val_518_);
lean_inc_ref(v_recoveredErrors_513_);
lean_inc_ref(v_cache_511_);
lean_inc(v_pos_510_);
lean_inc(v_lhsPrec_509_);
lean_inc_ref(v_stxStack_508_);
lean_dec_ref(v_s_504_);
if (v_mergeErrors_507_ == 0)
{
lean_dec_ref(v_error1_505_);
v___y_515_ = v_val_518_;
goto v___jp_514_;
}
else
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Parser_Error_merge(v_error1_505_, v_val_518_);
v___y_515_ = v___x_520_;
goto v___jp_514_;
}
}
}
else
{
lean_dec_ref(v_error1_505_);
return v_s_504_;
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___y_515_);
v___x_517_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_517_, 0, v_stxStack_508_);
lean_ctor_set(v___x_517_, 1, v_lhsPrec_509_);
lean_ctor_set(v___x_517_, 2, v_pos_510_);
lean_ctor_set(v___x_517_, 3, v_cache_511_);
lean_ctor_set(v___x_517_, 4, v___x_516_);
lean_ctor_set(v___x_517_, 5, v_recoveredErrors_513_);
return v___x_517_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mergeOrElseErrors_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_504_ = stack[0].m_obj;
lean_object* v_error1_505_ = stack[1].m_obj;
lean_object* v_iniPos_506_ = stack[2].m_obj;
uint8_t v_mergeErrors_507_ = stack[3].m_num;
lean_object* v_res_521_;
v_res_521_ = l_Lean_Parser_mergeOrElseErrors(v_s_504_, v_error1_505_, v_iniPos_506_, v_mergeErrors_507_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* v_s_522_, lean_object* v_error1_523_, lean_object* v_iniPos_524_, lean_object* v_mergeErrors_525_){
_start:
{
uint8_t v_mergeErrors_boxed_526_; lean_object* v_res_527_; 
v_mergeErrors_boxed_526_ = lean_unbox(v_mergeErrors_525_);
v_res_527_ = l_Lean_Parser_mergeOrElseErrors(v_s_522_, v_error1_523_, v_iniPos_524_, v_mergeErrors_boxed_526_);
lean_dec(v_iniPos_524_);
return v_res_527_;
}
}
lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl(uint8_t v_x_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_box(v_x_528_);
v___x_530_ = lean_obj_tag_nat(v___x_529_);
lean_dec(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT void l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_528_ = stack[0].m_num;
lean_object* v_res_531_;
v_res_531_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl(v_x_528_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl___boxed(lean_object* v_x_532_){
_start:
{
uint8_t v_x_4__boxed_533_; lean_object* v_res_534_; 
v_x_4__boxed_533_ = lean_unbox(v_x_532_);
v_res_534_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorIdx___impl(v_x_4__boxed_533_);
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
lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_object* v_motive_538_, lean_object* v_ctorIdx_539_, uint8_t v_t_540_, lean_object* v_h_541_, lean_object* v_k_542_){
_start:
{
lean_inc(v_k_542_);
return v_k_542_;
}
}
LEAN_EXPORT void l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_539_ = stack[1].m_obj;
uint8_t v_t_540_ = stack[2].m_num;
lean_object* v_k_542_ = stack[4].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(lean_box(0), v_ctorIdx_539_, v_t_540_, lean_box(0), v_k_542_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim___boxed(lean_object* v_motive_544_, lean_object* v_ctorIdx_545_, lean_object* v_t_546_, lean_object* v_h_547_, lean_object* v_k_548_){
_start:
{
uint8_t v_t_boxed_549_; lean_object* v_res_550_; 
v_t_boxed_549_ = lean_unbox(v_t_546_);
v_res_550_ = l_Lean_Parser_OrElseOnAntiquotBehavior_ctorElim(v_motive_544_, v_ctorIdx_545_, v_t_boxed_549_, v_h_547_, v_k_548_);
lean_dec(v_k_548_);
lean_dec(v_ctorIdx_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(lean_object* v_acceptLhs_551_){
_start:
{
lean_inc(v_acceptLhs_551_);
return v_acceptLhs_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg___boxed(lean_object* v_acceptLhs_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim___redArg(v_acceptLhs_552_);
lean_dec(v_acceptLhs_552_);
return v_res_553_;
}
}
lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_object* v_motive_554_, uint8_t v_t_555_, lean_object* v_h_556_, lean_object* v_acceptLhs_557_){
_start:
{
lean_inc(v_acceptLhs_557_);
return v_acceptLhs_557_;
}
}
LEAN_EXPORT void l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_555_ = stack[1].m_num;
lean_object* v_acceptLhs_557_ = stack[3].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Parser_OrElseOnAntiquotBehavior_acceptLhs_elim(lean_box(0), v_t_555_, lean_box(0), v_acceptLhs_557_);
stack->m_obj
 = v_res_558_;
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
lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_object* v_motive_568_, uint8_t v_t_569_, lean_object* v_h_570_, lean_object* v_takeLongest_571_){
_start:
{
lean_inc(v_takeLongest_571_);
return v_takeLongest_571_;
}
}
LEAN_EXPORT void l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_569_ = stack[1].m_num;
lean_object* v_takeLongest_571_ = stack[3].m_obj;
lean_object* v_res_572_;
v_res_572_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(lean_box(0), v_t_569_, lean_box(0), v_takeLongest_571_);
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim___boxed(lean_object* v_motive_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_takeLongest_576_){
_start:
{
uint8_t v_t_boxed_577_; lean_object* v_res_578_; 
v_t_boxed_577_ = lean_unbox(v_t_574_);
v_res_578_ = l_Lean_Parser_OrElseOnAntiquotBehavior_takeLongest_elim(v_motive_573_, v_t_boxed_577_, v_h_575_, v_takeLongest_576_);
lean_dec(v_takeLongest_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(lean_object* v_merge_579_){
_start:
{
lean_inc(v_merge_579_);
return v_merge_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg___boxed(lean_object* v_merge_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___redArg(v_merge_580_);
lean_dec(v_merge_580_);
return v_res_581_;
}
}
lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_object* v_motive_582_, uint8_t v_t_583_, lean_object* v_h_584_, lean_object* v_merge_585_){
_start:
{
lean_inc(v_merge_585_);
return v_merge_585_;
}
}
LEAN_EXPORT void l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_583_ = stack[1].m_num;
lean_object* v_merge_585_ = stack[3].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(lean_box(0), v_t_583_, lean_box(0), v_merge_585_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim___boxed(lean_object* v_motive_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_merge_590_){
_start:
{
uint8_t v_t_boxed_591_; lean_object* v_res_592_; 
v_t_boxed_591_ = lean_unbox(v_t_588_);
v_res_592_ = l_Lean_Parser_OrElseOnAntiquotBehavior_merge_elim(v_motive_587_, v_t_boxed_591_, v_h_589_, v_merge_590_);
lean_dec(v_merge_590_);
return v_res_592_;
}
}
uint8_t l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(uint8_t v_x_593_, uint8_t v_y_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_595_ = lean_box(v_x_593_);
v___x_596_ = lean_obj_tag_nat(v___x_595_);
lean_dec(v___x_595_);
v___x_597_ = lean_box(v_y_594_);
v___x_598_ = lean_obj_tag_nat(v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = lean_nat_dec_eq(v___x_596_, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT void l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_593_ = stack[0].m_num;
uint8_t v_y_594_ = stack[1].m_num;
uint8_t v_res_600_;
v_res_600_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_593_, v_y_594_);
stack->m_num = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq___boxed(lean_object* v_x_601_, lean_object* v_y_602_){
_start:
{
uint8_t v_x_24__boxed_603_; uint8_t v_y_25__boxed_604_; uint8_t v_res_605_; lean_object* v_r_606_; 
v_x_24__boxed_603_ = lean_unbox(v_x_601_);
v_y_25__boxed_604_ = lean_unbox(v_y_602_);
v_res_605_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_x_24__boxed_603_, v_y_25__boxed_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object* v_stx_612_, lean_object* v_s_613_){
_start:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
lean_inc(v_stx_612_);
v___x_615_ = l_Lean_Syntax_isOfKind(v_stx_612_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Parser_ParserState_pushSyntax(v_s_613_, v_stx_612_);
return v___x_616_;
}
else
{
lean_object* v_stxStack_617_; lean_object* v_lhsPrec_618_; lean_object* v_pos_619_; lean_object* v_cache_620_; lean_object* v_errorMsg_621_; lean_object* v_recoveredErrors_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_640_; 
v_stxStack_617_ = lean_ctor_get(v_s_613_, 0);
v_lhsPrec_618_ = lean_ctor_get(v_s_613_, 1);
v_pos_619_ = lean_ctor_get(v_s_613_, 2);
v_cache_620_ = lean_ctor_get(v_s_613_, 3);
v_errorMsg_621_ = lean_ctor_get(v_s_613_, 4);
v_recoveredErrors_622_ = lean_ctor_get(v_s_613_, 5);
v_isSharedCheck_640_ = !lean_is_exclusive(v_s_613_);
if (v_isSharedCheck_640_ == 0)
{
v___x_624_ = v_s_613_;
v_isShared_625_ = v_isSharedCheck_640_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_recoveredErrors_622_);
lean_inc(v_errorMsg_621_);
lean_inc(v_cache_620_);
lean_inc(v_pos_619_);
lean_inc(v_lhsPrec_618_);
lean_inc(v_stxStack_617_);
lean_dec(v_s_613_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_640_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_raw_626_; lean_object* v_drop_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_639_; 
v_raw_626_ = lean_ctor_get(v_stxStack_617_, 0);
v_drop_627_ = lean_ctor_get(v_stxStack_617_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_stxStack_617_);
if (v_isSharedCheck_639_ == 0)
{
v___x_629_ = v_stxStack_617_;
v_isShared_630_ = v_isSharedCheck_639_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_drop_627_);
lean_inc(v_raw_626_);
lean_dec(v_stxStack_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_639_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_631_ = l_Lean_Syntax_getArgs(v_stx_612_);
lean_dec(v_stx_612_);
v___x_632_ = l_Array_append___redArg(v_raw_626_, v___x_631_);
lean_dec_ref(v___x_631_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_632_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_drop_627_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_634_);
v___x_636_ = v___x_624_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_lhsPrec_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_pos_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_cache_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_errorMsg_621_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_recoveredErrors_622_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
}
lean_object* l_Lean_Parser_orelseFnCore(lean_object* v_p_641_, lean_object* v_q_642_, uint8_t v_antiquotBehavior_643_, lean_object* v_c_644_, lean_object* v_s_645_){
_start:
{
lean_object* v_pos_646_; lean_object* v_iniSz_647_; lean_object* v_s_648_; lean_object* v_errorMsg_649_; 
v_pos_646_ = lean_ctor_get(v_s_645_, 2);
lean_inc(v_pos_646_);
v_iniSz_647_ = l_Lean_Parser_ParserState_stackSize(v_s_645_);
lean_inc_ref(v_c_644_);
v_s_648_ = lean_apply_2(v_p_641_, v_c_644_, v_s_645_);
v_errorMsg_649_ = lean_ctor_get(v_s_648_, 4);
lean_inc(v_errorMsg_649_);
if (lean_obj_tag(v_errorMsg_649_) == 0)
{
lean_object* v_stxStack_650_; lean_object* v_pos_651_; lean_object* v_pBack_652_; lean_object* v___y_654_; uint8_t v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; uint8_t v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; uint8_t v___y_680_; uint8_t v___x_697_; uint8_t v___x_698_; 
v_stxStack_650_ = lean_ctor_get(v_s_648_, 0);
lean_inc_ref(v_stxStack_650_);
v_pos_651_ = lean_ctor_get(v_s_648_, 2);
lean_inc(v_pos_651_);
v_pBack_652_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_650_);
lean_dec_ref(v_stxStack_650_);
v___x_697_ = 0;
v___x_698_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_643_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_699_ = l_Lean_Parser_ParserState_stackSize(v_s_648_);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_add(v_iniSz_647_, v___x_700_);
v___x_702_ = lean_nat_dec_eq(v___x_699_, v___x_701_);
lean_dec(v___x_701_);
lean_dec(v___x_699_);
if (v___x_702_ == 0)
{
lean_dec(v_pBack_652_);
lean_dec(v_pos_651_);
lean_dec(v_iniSz_647_);
lean_dec(v_pos_646_);
lean_dec_ref(v_c_644_);
lean_dec_ref(v_q_642_);
return v_s_648_;
}
else
{
v___y_680_ = v___x_698_;
goto v___jp_679_;
}
}
else
{
v___y_680_ = v___x_698_;
goto v___jp_679_;
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = l_Lean_Parser_ParserState_restore(v___y_654_, v_iniSz_647_, v_pos_651_);
lean_dec(v_iniSz_647_);
v___x_656_ = l_Lean_Parser_ParserState_pushSyntax(v___x_655_, v_pBack_652_);
return v___x_656_;
}
v___jp_657_:
{
if (v___y_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = l_Lean_Parser_SyntaxStack_back(v___y_659_);
lean_dec_ref(v___y_659_);
lean_inc(v___x_662_);
v___x_663_ = l_Lean_Syntax_isAntiquots(v___x_662_);
if (v___x_663_ == 0)
{
lean_dec(v___x_662_);
v___y_654_ = v___y_660_;
goto v___jp_653_;
}
else
{
if (v___y_658_ == 0)
{
lean_object* v_s_664_; lean_object* v_s_665_; lean_object* v_s_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_pos_651_);
v_s_664_ = l_Lean_Parser_ParserState_popSyntax(v___y_660_);
v_s_665_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_652_, v_s_664_);
v_s_666_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_662_, v_s_665_);
v___x_667_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_668_ = l_Lean_Parser_ParserState_mkNode(v_s_666_, v___x_667_, v_iniSz_647_);
lean_dec(v_iniSz_647_);
return v___x_668_;
}
else
{
lean_dec(v___x_662_);
v___y_654_ = v___y_660_;
goto v___jp_653_;
}
}
}
else
{
lean_dec_ref(v___y_659_);
v___y_654_ = v___y_660_;
goto v___jp_653_;
}
}
v___jp_669_:
{
if (v___y_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_675_ = l_Lean_Parser_ParserState_stackSize(v___y_673_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_iniSz_647_, v___x_676_);
v___x_678_ = lean_nat_dec_eq(v___x_675_, v___x_677_);
lean_dec(v___x_677_);
lean_dec(v___x_675_);
if (v___x_678_ == 0)
{
v___y_658_ = v___y_670_;
v___y_659_ = v___y_672_;
v___y_660_ = v___y_673_;
v___y_661_ = v___y_671_;
goto v___jp_657_;
}
else
{
v___y_658_ = v___y_670_;
v___y_659_ = v___y_672_;
v___y_660_ = v___y_673_;
v___y_661_ = v___y_670_;
goto v___jp_657_;
}
}
else
{
lean_dec_ref(v___y_672_);
v___y_654_ = v___y_673_;
goto v___jp_653_;
}
}
v___jp_679_:
{
if (v___y_680_ == 0)
{
uint8_t v___x_681_; 
lean_inc(v_pBack_652_);
v___x_681_ = l_Lean_Syntax_isAntiquots(v_pBack_652_);
if (v___x_681_ == 0)
{
lean_dec(v_pBack_652_);
lean_dec(v_pos_651_);
lean_dec(v_iniSz_647_);
lean_dec(v_pos_646_);
lean_dec_ref(v_c_644_);
lean_dec_ref(v_q_642_);
return v_s_648_;
}
else
{
lean_object* v_s_682_; lean_object* v_s_683_; lean_object* v_stxStack_684_; lean_object* v_pos_685_; lean_object* v_errorMsg_686_; uint8_t v___x_687_; 
v_s_682_ = l_Lean_Parser_ParserState_restore(v_s_648_, v_iniSz_647_, v_pos_646_);
v_s_683_ = lean_apply_2(v_q_642_, v_c_644_, v_s_682_);
v_stxStack_684_ = lean_ctor_get(v_s_683_, 0);
lean_inc_ref(v_stxStack_684_);
v_pos_685_ = lean_ctor_get(v_s_683_, 2);
lean_inc(v_pos_685_);
v_errorMsg_686_ = lean_ctor_get(v_s_683_, 4);
lean_inc(v_errorMsg_686_);
v___x_687_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_686_, v_errorMsg_649_);
lean_dec(v_errorMsg_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_pos_685_);
lean_dec_ref(v_stxStack_684_);
v___x_688_ = l_Lean_Parser_ParserState_restore(v_s_683_, v_iniSz_647_, v_pos_651_);
lean_dec(v_iniSz_647_);
v___x_689_ = l_Lean_Parser_ParserState_pushSyntax(v___x_688_, v_pBack_652_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_add(v_pos_651_, v___x_690_);
v___x_692_ = lean_nat_dec_le(v___x_691_, v_pos_685_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_nat_add(v_pos_685_, v___x_690_);
lean_dec(v_pos_685_);
v___x_694_ = lean_nat_dec_le(v___x_693_, v_pos_651_);
lean_dec(v___x_693_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = 2;
v___x_696_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_643_, v___x_695_);
if (v___x_696_ == 0)
{
v___y_670_ = v___x_692_;
v___y_671_ = v___x_687_;
v___y_672_ = v_stxStack_684_;
v___y_673_ = v_s_683_;
v___y_674_ = v___x_687_;
goto v___jp_669_;
}
else
{
v___y_670_ = v___x_692_;
v___y_671_ = v___x_687_;
v___y_672_ = v_stxStack_684_;
v___y_673_ = v_s_683_;
v___y_674_ = v___x_692_;
goto v___jp_669_;
}
}
else
{
v___y_670_ = v___x_692_;
v___y_671_ = v___x_687_;
v___y_672_ = v_stxStack_684_;
v___y_673_ = v_s_683_;
v___y_674_ = v___x_694_;
goto v___jp_669_;
}
}
else
{
lean_dec(v_pos_685_);
lean_dec_ref(v_stxStack_684_);
lean_dec(v_pBack_652_);
lean_dec(v_pos_651_);
lean_dec(v_iniSz_647_);
return v_s_683_;
}
}
}
}
else
{
lean_dec(v_pBack_652_);
lean_dec(v_pos_651_);
lean_dec(v_iniSz_647_);
lean_dec(v_pos_646_);
lean_dec_ref(v_c_644_);
lean_dec_ref(v_q_642_);
return v_s_648_;
}
}
}
else
{
lean_object* v_pos_703_; lean_object* v_val_704_; uint8_t v_decide_705_; 
v_pos_703_ = lean_ctor_get(v_s_648_, 2);
lean_inc(v_pos_703_);
v_val_704_ = lean_ctor_get(v_errorMsg_649_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_errorMsg_649_, 1);
v_decide_705_ = lean_nat_dec_eq(v_pos_703_, v_pos_646_);
lean_dec(v_pos_703_);
if (v_decide_705_ == 0)
{
lean_dec(v_val_704_);
lean_dec(v_iniSz_647_);
lean_dec(v_pos_646_);
lean_dec_ref(v_c_644_);
lean_dec_ref(v_q_642_);
return v_s_648_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_inc(v_pos_646_);
v___x_706_ = l_Lean_Parser_ParserState_restore(v_s_648_, v_iniSz_647_, v_pos_646_);
lean_dec(v_iniSz_647_);
v___x_707_ = lean_apply_2(v_q_642_, v_c_644_, v___x_706_);
v___x_708_ = l_Lean_Parser_mergeOrElseErrors(v___x_707_, v_val_704_, v_pos_646_, v_decide_705_);
lean_dec(v_pos_646_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_orelseFnCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_641_ = stack[0].m_obj;
lean_object* v_q_642_ = stack[1].m_obj;
uint8_t v_antiquotBehavior_643_ = stack[2].m_num;
lean_object* v_c_644_ = stack[3].m_obj;
lean_object* v_s_645_ = stack[4].m_obj;
lean_object* v_res_709_;
v_res_709_ = l_Lean_Parser_orelseFnCore(v_p_641_, v_q_642_, v_antiquotBehavior_643_, v_c_644_, v_s_645_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_710_, lean_object* v_q_711_, lean_object* v_antiquotBehavior_712_, lean_object* v_c_713_, lean_object* v_s_714_){
_start:
{
uint8_t v_antiquotBehavior_boxed_715_; lean_object* v_res_716_; 
v_antiquotBehavior_boxed_715_ = lean_unbox(v_antiquotBehavior_712_);
v_res_716_ = l_Lean_Parser_orelseFnCore(v_p_710_, v_q_711_, v_antiquotBehavior_boxed_715_, v_c_713_, v_s_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_717_, lean_object* v_q_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
uint8_t v___x_721_; lean_object* v___x_722_; 
v___x_721_ = 2;
v___x_722_ = l_Lean_Parser_orelseFnCore(v_p_717_, v_q_718_, v___x_721_, v_a_719_, v_a_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_723_, lean_object* v_q_724_){
_start:
{
lean_object* v_collectTokens_725_; lean_object* v_collectKinds_726_; lean_object* v_firstTokens_727_; lean_object* v_collectTokens_728_; lean_object* v_collectKinds_729_; lean_object* v_firstTokens_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_740_; 
v_collectTokens_725_ = lean_ctor_get(v_p_723_, 0);
lean_inc_ref(v_collectTokens_725_);
v_collectKinds_726_ = lean_ctor_get(v_p_723_, 1);
lean_inc_ref(v_collectKinds_726_);
v_firstTokens_727_ = lean_ctor_get(v_p_723_, 2);
lean_inc(v_firstTokens_727_);
lean_dec_ref(v_p_723_);
v_collectTokens_728_ = lean_ctor_get(v_q_724_, 0);
v_collectKinds_729_ = lean_ctor_get(v_q_724_, 1);
v_firstTokens_730_ = lean_ctor_get(v_q_724_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_q_724_);
if (v_isSharedCheck_740_ == 0)
{
v___x_732_ = v_q_724_;
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_firstTokens_730_);
lean_inc(v_collectKinds_729_);
lean_inc(v_collectTokens_728_);
lean_dec(v_q_724_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_734_, 0, v_collectKinds_729_);
lean_closure_set(v___f_734_, 1, v_collectKinds_726_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_735_, 0, v_collectTokens_728_);
lean_closure_set(v___f_735_, 1, v_collectTokens_725_);
v___x_736_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_727_, v_firstTokens_730_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 2, v___x_736_);
lean_ctor_set(v___x_732_, 1, v___f_734_);
lean_ctor_set(v___x_732_, 0, v___f_735_);
v___x_738_ = v___x_732_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___f_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___f_734_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_741_, lean_object* v_p2_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_apply_1(v_p2_742_, v___x_745_);
v___x_747_ = l_Lean_Parser_orelseFn(v_p1_741_, v___x_746_, v___y_743_, v___y_744_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_750_, lean_object* v_q_751_){
_start:
{
lean_object* v_info_752_; lean_object* v_fn_753_; lean_object* v_info_754_; lean_object* v_fn_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_764_; 
v_info_752_ = lean_ctor_get(v_p_750_, 0);
lean_inc_ref(v_info_752_);
v_fn_753_ = lean_ctor_get(v_p_750_, 1);
lean_inc_ref(v_fn_753_);
lean_dec_ref(v_p_750_);
v_info_754_ = lean_ctor_get(v_q_751_, 0);
v_fn_755_ = lean_ctor_get(v_q_751_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_q_751_);
if (v_isSharedCheck_764_ == 0)
{
v___x_757_ = v_q_751_;
v_isShared_758_ = v_isSharedCheck_764_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_fn_755_);
lean_inc(v_info_754_);
lean_dec(v_q_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_764_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_759_ = l_Lean_Parser_orelseInfo(v_info_752_, v_info_754_);
v___x_760_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_760_, 0, v_fn_753_);
lean_closure_set(v___x_760_, 1, v_fn_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_760_);
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_762_ = v___x_757_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_773_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_774_ = l_Lean_addBuiltinDocString(v___x_772_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_775_;
v_res_775_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_778_, lean_object* v_b_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_box(0);
v___x_781_ = lean_apply_1(v_b_779_, v___x_780_);
v___x_782_ = l_Lean_Parser_orelse(v_a_778_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_785_){
_start:
{
lean_object* v_collectTokens_786_; lean_object* v_collectKinds_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_collectTokens_786_ = lean_ctor_get(v_info_785_, 0);
v_collectKinds_787_ = lean_ctor_get(v_info_785_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_info_785_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_info_785_, 2);
lean_dec(v_unused_796_);
v___x_789_ = v_info_785_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_collectKinds_787_);
lean_inc(v_collectTokens_786_);
lean_dec(v_info_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_box(1);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_collectTokens_786_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_collectKinds_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_797_, lean_object* v_c_798_, lean_object* v_s_799_){
_start:
{
lean_object* v_pos_800_; lean_object* v___x_801_; lean_object* v_errorMsg_802_; 
v_pos_800_ = lean_ctor_get(v_s_799_, 2);
lean_inc(v_pos_800_);
v___x_801_ = lean_apply_2(v_p_797_, v_c_798_, v_s_799_);
v_errorMsg_802_ = lean_ctor_get(v___x_801_, 4);
lean_inc(v_errorMsg_802_);
if (lean_obj_tag(v_errorMsg_802_) == 1)
{
lean_object* v_stxStack_803_; lean_object* v_lhsPrec_804_; lean_object* v_cache_805_; lean_object* v_recoveredErrors_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_stxStack_803_ = lean_ctor_get(v___x_801_, 0);
v_lhsPrec_804_ = lean_ctor_get(v___x_801_, 1);
v_cache_805_ = lean_ctor_get(v___x_801_, 3);
v_recoveredErrors_806_ = lean_ctor_get(v___x_801_, 5);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; lean_object* v_unused_815_; 
v_unused_814_ = lean_ctor_get(v___x_801_, 4);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v___x_801_, 2);
lean_dec(v_unused_815_);
v___x_808_ = v___x_801_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_recoveredErrors_806_);
lean_inc(v_cache_805_);
lean_inc(v_lhsPrec_804_);
lean_inc(v_stxStack_803_);
lean_dec(v___x_801_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 2, v_pos_800_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_stxStack_803_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_lhsPrec_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_pos_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_cache_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_errorMsg_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 5, v_recoveredErrors_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_dec(v_errorMsg_802_);
lean_dec(v_pos_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_816_){
_start:
{
lean_object* v_info_817_; lean_object* v_fn_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_info_817_ = lean_ctor_get(v_p_816_, 0);
v_fn_818_ = lean_ctor_get(v_p_816_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_p_816_);
if (v_isSharedCheck_826_ == 0)
{
v___x_820_ = v_p_816_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_fn_818_);
lean_inc(v_info_817_);
lean_dec(v_p_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_822_, 0, v_fn_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_info_817_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_835_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_836_ = l_Lean_addBuiltinDocString(v___x_834_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_837_;
v_res_837_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_839_;
}
}
uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_840_, lean_object* v_x_841_){
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
LEAN_EXPORT void l_Lean_Parser_instBEqRecoveryContext_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_840_ = stack[0].m_obj;
lean_object* v_x_841_ = stack[1].m_obj;
uint8_t v_res_848_;
v_res_848_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_840_, v_x_841_);
stack->m_num = v_res_848_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_849_, v_x_850_);
lean_dec_ref(v_x_850_);
lean_dec_ref(v_x_849_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
lean_object* v_initialPos_857_; lean_object* v_initialSize_858_; lean_object* v_initialPos_859_; lean_object* v_initialSize_860_; uint8_t v_decide_861_; 
v_initialPos_857_ = lean_ctor_get(v_x_855_, 0);
v_initialSize_858_ = lean_ctor_get(v_x_855_, 1);
v_initialPos_859_ = lean_ctor_get(v_x_856_, 0);
v_initialSize_860_ = lean_ctor_get(v_x_856_, 1);
v_decide_861_ = lean_nat_dec_eq(v_initialPos_857_, v_initialPos_859_);
if (v_decide_861_ == 0)
{
return v_decide_861_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = lean_nat_dec_eq(v_initialSize_858_, v_initialSize_860_);
return v___x_862_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_instDecidableEqRecoveryContext_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_855_ = stack[0].m_obj;
lean_object* v_x_856_ = stack[1].m_obj;
uint8_t v_res_863_;
v_res_863_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_855_, v_x_856_);
stack->m_num = v_res_863_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_864_, v_x_865_);
lean_dec_ref(v_x_865_);
lean_dec_ref(v_x_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT void l_Lean_Parser_instDecidableEqRecoveryContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_868_ = stack[0].m_obj;
lean_object* v_x_869_ = stack[1].m_obj;
uint8_t v_res_871_;
v_res_871_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_868_, v_x_869_);
stack->m_num = v_res_871_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_872_, v_x_873_);
lean_dec_ref(v_x_873_);
lean_dec_ref(v_x_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_unsigned_to_nat(14u);
v___x_890_ = lean_nat_to_int(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(15u);
v___x_904_ = lean_nat_to_int(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_906_ = lean_string_length(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_908_ = lean_nat_to_int(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_911_){
_start:
{
lean_object* v_initialPos_912_; lean_object* v_initialSize_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_951_; 
v_initialPos_912_ = lean_ctor_get(v_x_911_, 0);
v_initialSize_913_ = lean_ctor_get(v_x_911_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_951_ == 0)
{
v___x_915_ = v_x_911_;
v_isShared_916_ = v_isSharedCheck_951_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_initialSize_913_);
lean_inc(v_initialPos_912_);
lean_dec(v_x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_951_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_917_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_918_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_919_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_920_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_921_ = l_Nat_reprFast(v_initialPos_912_);
v___x_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 5);
lean_ctor_set(v___x_915_, 1, v___x_922_);
lean_ctor_set(v___x_915_, 0, v___x_920_);
v___x_924_ = v___x_915_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_950_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_925_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_919_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = 0;
v___x_929_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*1, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_918_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_box(1);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_917_);
v___x_938_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_939_ = l_Nat_reprFast(v_initialSize_913_);
v___x_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
v___x_941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_938_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_928_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_937_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_945_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_943_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_925_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_944_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_928_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_952_, lean_object* v_prec_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_955_, lean_object* v_prec_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_955_, v_prec_956_);
lean_dec(v_prec_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_960_, lean_object* v_recover_961_, lean_object* v_c_962_, lean_object* v_s_963_){
_start:
{
lean_object* v_stxStack_964_; lean_object* v_pos_965_; lean_object* v_s_966_; lean_object* v_errorMsg_967_; 
v_stxStack_964_ = lean_ctor_get(v_s_963_, 0);
lean_inc_ref(v_stxStack_964_);
v_pos_965_ = lean_ctor_get(v_s_963_, 2);
lean_inc(v_pos_965_);
lean_inc_ref(v_c_962_);
v_s_966_ = lean_apply_2(v_p_960_, v_c_962_, v_s_963_);
v_errorMsg_967_ = lean_ctor_get(v_s_966_, 4);
lean_inc(v_errorMsg_967_);
if (lean_obj_tag(v_errorMsg_967_) == 1)
{
lean_object* v_stxStack_968_; lean_object* v_lhsPrec_969_; lean_object* v_pos_970_; lean_object* v_cache_971_; lean_object* v_recoveredErrors_972_; lean_object* v_val_973_; lean_object* v_iniSz_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_s_x27_978_; lean_object* v_stxStack_979_; lean_object* v_pos_980_; lean_object* v_errorMsg_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_992_; 
v_stxStack_968_ = lean_ctor_get(v_s_966_, 0);
lean_inc_ref(v_stxStack_968_);
v_lhsPrec_969_ = lean_ctor_get(v_s_966_, 1);
lean_inc_n(v_lhsPrec_969_, 2);
v_pos_970_ = lean_ctor_get(v_s_966_, 2);
lean_inc(v_pos_970_);
v_cache_971_ = lean_ctor_get(v_s_966_, 3);
lean_inc_ref_n(v_cache_971_, 2);
v_recoveredErrors_972_ = lean_ctor_get(v_s_966_, 5);
lean_inc_ref_n(v_recoveredErrors_972_, 2);
v_val_973_ = lean_ctor_get(v_errorMsg_967_, 0);
lean_inc(v_val_973_);
lean_dec_ref_known(v_errorMsg_967_, 1);
v_iniSz_974_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_964_);
lean_dec_ref(v_stxStack_964_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_pos_965_);
lean_ctor_set(v___x_975_, 1, v_iniSz_974_);
v___x_976_ = lean_box(0);
v___x_977_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_977_, 0, v_stxStack_968_);
lean_ctor_set(v___x_977_, 1, v_lhsPrec_969_);
lean_ctor_set(v___x_977_, 2, v_pos_970_);
lean_ctor_set(v___x_977_, 3, v_cache_971_);
lean_ctor_set(v___x_977_, 4, v___x_976_);
lean_ctor_set(v___x_977_, 5, v_recoveredErrors_972_);
v_s_x27_978_ = lean_apply_3(v_recover_961_, v___x_975_, v_c_962_, v___x_977_);
v_stxStack_979_ = lean_ctor_get(v_s_x27_978_, 0);
v_pos_980_ = lean_ctor_get(v_s_x27_978_, 2);
v_errorMsg_981_ = lean_ctor_get(v_s_x27_978_, 4);
v_isSharedCheck_992_ = !lean_is_exclusive(v_s_x27_978_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_993_ = lean_ctor_get(v_s_x27_978_, 5);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_s_x27_978_, 3);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_s_x27_978_, 1);
lean_dec(v_unused_995_);
v___x_983_ = v_s_x27_978_;
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_errorMsg_981_);
lean_inc(v_pos_980_);
lean_inc(v_stxStack_979_);
lean_dec(v_s_x27_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v___x_985_; 
v___x_985_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_981_, v___x_976_);
lean_dec(v_errorMsg_981_);
if (v___x_985_ == 0)
{
lean_del_object(v___x_983_);
lean_dec(v_pos_980_);
lean_dec_ref(v_stxStack_979_);
lean_dec(v_val_973_);
lean_dec_ref(v_recoveredErrors_972_);
lean_dec_ref(v_cache_971_);
lean_dec(v_lhsPrec_969_);
return v_s_966_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec_ref(v_s_966_);
lean_inc_ref(v_stxStack_979_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_stxStack_979_);
lean_ctor_set(v___x_986_, 1, v_val_973_);
lean_inc(v_pos_980_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_pos_980_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_array_push(v_recoveredErrors_972_, v___x_987_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 5, v___x_988_);
lean_ctor_set(v___x_983_, 4, v___x_976_);
lean_ctor_set(v___x_983_, 3, v_cache_971_);
lean_ctor_set(v___x_983_, 1, v_lhsPrec_969_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_stxStack_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_lhsPrec_969_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_pos_980_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_cache_971_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_991_, 5, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_dec(v_errorMsg_967_);
lean_dec(v_pos_965_);
lean_dec_ref(v_stxStack_964_);
lean_dec_ref(v_c_962_);
lean_dec_ref(v_recover_961_);
return v_s_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_996_, lean_object* v_s_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v_fn_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_apply_1(v_handler_996_, v_s_997_);
v_fn_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc_ref(v_fn_1001_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = lean_apply_2(v_fn_1001_, v___y_998_, v___y_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_1003_, lean_object* v_handler_1004_){
_start:
{
lean_object* v_info_1005_; lean_object* v_fn_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1015_; 
v_info_1005_ = lean_ctor_get(v_parser_1003_, 0);
v_fn_1006_ = lean_ctor_get(v_parser_1003_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_parser_1003_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1008_ = v_parser_1003_;
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_fn_1006_);
lean_inc(v_info_1005_);
lean_dec(v_parser_1003_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_1010_, 0, v_handler_1004_);
v___x_1011_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_1011_, 0, v_fn_1006_);
lean_closure_set(v___x_1011_, 1, v___f_1010_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_info_1005_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_1024_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_1025_ = l_Lean_addBuiltinDocString(v___x_1023_, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1026_;
v_res_1026_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_1029_, lean_object* v_x_1030_){
_start:
{
lean_inc_ref(v_handler_1029_);
return v_handler_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Parser_recover___lam__0(v_handler_1031_, v_x_1032_);
lean_dec_ref(v_x_1032_);
lean_dec_ref(v_handler_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_1034_, lean_object* v_handler_1035_){
_start:
{
lean_object* v___f_1036_; lean_object* v___x_1037_; 
v___f_1036_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1036_, 0, v_handler_1035_);
v___x_1037_ = l_Lean_Parser_recover_x27(v_parser_1034_, v___f_1036_);
return v___x_1037_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1046_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1047_ = l_Lean_addBuiltinDocString(v___x_1045_, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1048_;
v_res_1048_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
stack->m_obj
 = v_res_1048_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1054_, lean_object* v_c_1055_, lean_object* v_s_1056_){
_start:
{
lean_object* v_pos_1057_; lean_object* v_iniSz_1058_; lean_object* v___y_1060_; lean_object* v_s_1063_; lean_object* v_pos_1064_; lean_object* v_errorMsg_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_pos_1057_ = lean_ctor_get(v_s_1056_, 2);
lean_inc(v_pos_1057_);
v_iniSz_1058_ = l_Lean_Parser_ParserState_stackSize(v_s_1056_);
v_s_1063_ = lean_apply_2(v_p_1054_, v_c_1055_, v_s_1056_);
v_pos_1064_ = lean_ctor_get(v_s_1063_, 2);
lean_inc(v_pos_1064_);
v_errorMsg_1065_ = lean_ctor_get(v_s_1063_, 4);
lean_inc(v_errorMsg_1065_);
v___x_1066_ = lean_box(0);
v___x_1067_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1065_, v___x_1066_);
lean_dec(v_errorMsg_1065_);
if (v___x_1067_ == 0)
{
uint8_t v_decide_1068_; 
v_decide_1068_ = lean_nat_dec_eq(v_pos_1064_, v_pos_1057_);
lean_dec(v_pos_1064_);
if (v_decide_1068_ == 0)
{
lean_dec(v_pos_1057_);
v___y_1060_ = v_s_1063_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Parser_ParserState_restore(v_s_1063_, v_iniSz_1058_, v_pos_1057_);
v___y_1060_ = v___x_1069_;
goto v___jp_1059_;
}
}
else
{
lean_dec(v_pos_1064_);
lean_dec(v_pos_1057_);
v___y_1060_ = v_s_1063_;
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1062_ = l_Lean_Parser_ParserState_mkNode(v___y_1060_, v___x_1061_, v_iniSz_1058_);
lean_dec(v_iniSz_1058_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1070_){
_start:
{
lean_object* v_collectTokens_1071_; lean_object* v_collectKinds_1072_; lean_object* v_firstTokens_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_collectTokens_1071_ = lean_ctor_get(v_p_1070_, 0);
v_collectKinds_1072_ = lean_ctor_get(v_p_1070_, 1);
v_firstTokens_1073_ = lean_ctor_get(v_p_1070_, 2);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_p_1070_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v_p_1070_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_firstTokens_1073_);
lean_inc(v_collectKinds_1072_);
lean_inc(v_collectTokens_1071_);
lean_dec(v_p_1070_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 2, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_collectTokens_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_collectKinds_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1082_){
_start:
{
lean_object* v_info_1083_; lean_object* v_fn_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_info_1083_ = lean_ctor_get(v_p_1082_, 0);
v_fn_1084_ = lean_ctor_get(v_p_1082_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_p_1082_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v_p_1082_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_fn_1084_);
lean_inc(v_info_1083_);
lean_dec(v_p_1082_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = l_Lean_Parser_optionalInfo(v_info_1083_);
v___x_1089_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1089_, 0, v_fn_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v___x_1089_);
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1094_, lean_object* v_c_1095_, lean_object* v_s_1096_){
_start:
{
lean_object* v_pos_1097_; lean_object* v_iniSz_1098_; lean_object* v_s_1099_; lean_object* v_errorMsg_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_pos_1097_ = lean_ctor_get(v_s_1096_, 2);
lean_inc(v_pos_1097_);
v_iniSz_1098_ = l_Lean_Parser_ParserState_stackSize(v_s_1096_);
v_s_1099_ = lean_apply_2(v_p_1094_, v_c_1095_, v_s_1096_);
v_errorMsg_1100_ = lean_ctor_get(v_s_1099_, 4);
lean_inc(v_errorMsg_1100_);
v___x_1101_ = lean_box(0);
v___x_1102_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1100_, v___x_1101_);
lean_dec(v_errorMsg_1100_);
if (v___x_1102_ == 0)
{
lean_dec(v_iniSz_1098_);
lean_dec(v_pos_1097_);
return v_s_1099_;
}
else
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_Parser_ParserState_restore(v_s_1099_, v_iniSz_1098_, v_pos_1097_);
lean_dec(v_iniSz_1098_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1104_){
_start:
{
lean_object* v_info_1105_; lean_object* v_fn_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
v_info_1105_ = lean_ctor_get(v_p_1104_, 0);
v_fn_1106_ = lean_ctor_get(v_p_1104_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_p_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v_p_1104_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_fn_1106_);
lean_inc(v_info_1105_);
lean_dec(v_p_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1110_, 0, v_fn_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 1, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_info_1105_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1123_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1124_ = l_Lean_addBuiltinDocString(v___x_1122_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1125_;
v_res_1125_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1129_, lean_object* v_msg_1130_, lean_object* v_c_1131_, lean_object* v_s_1132_){
_start:
{
lean_object* v_pos_1133_; lean_object* v_iniSz_1134_; lean_object* v_s_1135_; lean_object* v_errorMsg_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_pos_1133_ = lean_ctor_get(v_s_1132_, 2);
lean_inc(v_pos_1133_);
v_iniSz_1134_ = l_Lean_Parser_ParserState_stackSize(v_s_1132_);
v_s_1135_ = lean_apply_2(v_p_1129_, v_c_1131_, v_s_1132_);
v_errorMsg_1136_ = lean_ctor_get(v_s_1135_, 4);
lean_inc(v_errorMsg_1136_);
v___x_1137_ = lean_box(0);
v___x_1138_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1136_, v___x_1137_);
lean_dec(v_errorMsg_1136_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Parser_ParserState_restore(v_s_1135_, v_iniSz_1134_, v_pos_1133_);
lean_dec(v_iniSz_1134_);
return v___x_1139_;
}
else
{
lean_object* v_s_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_s_1140_ = l_Lean_Parser_ParserState_restore(v_s_1135_, v_iniSz_1134_, v_pos_1133_);
lean_dec(v_iniSz_1134_);
v___x_1141_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1142_ = lean_string_append(v___x_1141_, v_msg_1130_);
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1140_, v___x_1142_, v___x_1143_, v___x_1138_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1145_, lean_object* v_msg_1146_, lean_object* v_c_1147_, lean_object* v_s_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Parser_notFollowedByFn(v_p_1145_, v_msg_1146_, v_c_1147_, v_s_1148_);
lean_dec_ref(v_msg_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1150_, lean_object* v_msg_1151_){
_start:
{
lean_object* v_fn_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1161_; 
v_fn_1152_ = lean_ctor_get(v_p_1150_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_p_1150_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_p_1150_, 0);
lean_dec(v_unused_1162_);
v___x_1154_ = v_p_1150_;
v_isShared_1155_ = v_isSharedCheck_1161_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_fn_1152_);
lean_dec(v_p_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1161_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1157_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1157_, 0, v_fn_1152_);
lean_closure_set(v___x_1157_, 1, v_msg_1151_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1157_);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1171_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1172_ = l_Lean_addBuiltinDocString(v___x_1170_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1173_;
v_res_1173_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1177_, lean_object* v_c_1178_, lean_object* v_s_1179_){
_start:
{
lean_object* v_pos_1180_; lean_object* v_iniSz_1181_; lean_object* v_s_1182_; lean_object* v_pos_1183_; lean_object* v_errorMsg_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_pos_1180_ = lean_ctor_get(v_s_1179_, 2);
lean_inc(v_pos_1180_);
v_iniSz_1181_ = l_Lean_Parser_ParserState_stackSize(v_s_1179_);
lean_inc_ref(v_p_1177_);
lean_inc_ref(v_c_1178_);
v_s_1182_ = lean_apply_2(v_p_1177_, v_c_1178_, v_s_1179_);
v_pos_1183_ = lean_ctor_get(v_s_1182_, 2);
lean_inc(v_pos_1183_);
v_errorMsg_1184_ = lean_ctor_get(v_s_1182_, 4);
lean_inc(v_errorMsg_1184_);
v___x_1185_ = lean_box(0);
v___x_1186_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1184_, v___x_1185_);
lean_dec(v_errorMsg_1184_);
if (v___x_1186_ == 0)
{
uint8_t v_decide_1187_; 
lean_dec_ref(v_c_1178_);
lean_dec_ref(v_p_1177_);
v_decide_1187_ = lean_nat_dec_eq(v_pos_1180_, v_pos_1183_);
lean_dec(v_pos_1183_);
if (v_decide_1187_ == 0)
{
lean_dec(v_iniSz_1181_);
lean_dec(v_pos_1180_);
return v_s_1182_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Parser_ParserState_restore(v_s_1182_, v_iniSz_1181_, v_pos_1180_);
lean_dec(v_iniSz_1181_);
return v___x_1188_;
}
}
else
{
uint8_t v_decide_1189_; 
v_decide_1189_ = lean_nat_dec_eq(v_pos_1180_, v_pos_1183_);
lean_dec(v_pos_1183_);
lean_dec(v_pos_1180_);
if (v_decide_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_iniSz_1181_, v___x_1190_);
v___x_1192_ = l_Lean_Parser_ParserState_stackSize(v_s_1182_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
lean_dec(v___x_1192_);
lean_dec(v___x_1191_);
if (v___x_1193_ == 0)
{
lean_dec(v_iniSz_1181_);
v_s_1179_ = v_s_1182_;
goto _start;
}
else
{
lean_object* v___x_1195_; lean_object* v_s_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1196_ = l_Lean_Parser_ParserState_mkNode(v_s_1182_, v___x_1195_, v_iniSz_1181_);
lean_dec(v_iniSz_1181_);
v_s_1179_ = v_s_1196_;
goto _start;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec(v_iniSz_1181_);
lean_dec_ref(v_c_1178_);
lean_dec_ref(v_p_1177_);
v___x_1198_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1199_ = lean_box(0);
v___x_1200_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1182_, v___x_1198_, v___x_1199_, v___x_1186_);
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1201_, lean_object* v_c_1202_, lean_object* v_s_1203_){
_start:
{
lean_object* v_iniSz_1204_; lean_object* v_s_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_iniSz_1204_ = l_Lean_Parser_ParserState_stackSize(v_s_1203_);
v_s_1205_ = l_Lean_Parser_manyAux(v_p_1201_, v_c_1202_, v_s_1203_);
v___x_1206_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1207_ = l_Lean_Parser_ParserState_mkNode(v_s_1205_, v___x_1206_, v_iniSz_1204_);
lean_dec(v_iniSz_1204_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1208_){
_start:
{
lean_object* v_info_1209_; lean_object* v_fn_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1219_; 
v_info_1209_ = lean_ctor_get(v_p_1208_, 0);
v_fn_1210_ = lean_ctor_get(v_p_1208_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_p_1208_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1212_ = v_p_1208_;
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_fn_1210_);
lean_inc(v_info_1209_);
lean_dec(v_p_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = l_Lean_Parser_noFirstTokenInfo(v_info_1209_);
v___x_1215_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1215_, 0, v_fn_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1215_);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1220_, lean_object* v_c_1221_, lean_object* v_s_1222_){
_start:
{
lean_object* v_iniSz_1223_; lean_object* v___x_1224_; lean_object* v_s_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_iniSz_1223_ = l_Lean_Parser_ParserState_stackSize(v_s_1222_);
lean_inc_ref(v_p_1220_);
v___x_1224_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1224_, 0, v_p_1220_);
v_s_1225_ = l_Lean_Parser_andthenFn(v_p_1220_, v___x_1224_, v_c_1221_, v_s_1222_);
v___x_1226_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1227_ = l_Lean_Parser_ParserState_mkNode(v_s_1225_, v___x_1226_, v_iniSz_1223_);
lean_dec(v_iniSz_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1228_){
_start:
{
lean_object* v_info_1229_; lean_object* v_fn_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
v_info_1229_ = lean_ctor_get(v_p_1228_, 0);
v_fn_1230_ = lean_ctor_get(v_p_1228_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_p_1228_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1232_ = v_p_1228_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_fn_1230_);
lean_inc(v_info_1229_);
lean_dec(v_p_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1234_, 0, v_fn_1230_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_info_1229_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1239_, lean_object* v_sep_1240_, uint8_t v_allowTrailingSep_1241_, lean_object* v_iniSz_1242_, uint8_t v_pOpt_1243_, lean_object* v_c_1244_, lean_object* v_s_1245_){
_start:
{
lean_object* v_s_1247_; lean_object* v_pos_1248_; lean_object* v_pos_1265_; lean_object* v_sz_1266_; lean_object* v_s_1267_; lean_object* v_pos_1268_; lean_object* v_errorMsg_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_pos_1265_ = lean_ctor_get(v_s_1245_, 2);
lean_inc(v_pos_1265_);
v_sz_1266_ = l_Lean_Parser_ParserState_stackSize(v_s_1245_);
lean_inc_ref(v_p_1239_);
lean_inc_ref(v_c_1244_);
v_s_1267_ = lean_apply_2(v_p_1239_, v_c_1244_, v_s_1245_);
v_pos_1268_ = lean_ctor_get(v_s_1267_, 2);
lean_inc(v_pos_1268_);
v_errorMsg_1269_ = lean_ctor_get(v_s_1267_, 4);
lean_inc(v_errorMsg_1269_);
v___x_1270_ = lean_box(0);
v___x_1271_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1269_, v___x_1270_);
lean_dec(v_errorMsg_1269_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
lean_dec_ref(v_c_1244_);
lean_dec_ref(v_sep_1240_);
lean_dec_ref(v_p_1239_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_add(v_pos_1265_, v___x_1272_);
v___x_1274_ = lean_nat_dec_le(v___x_1273_, v_pos_1268_);
lean_dec(v_pos_1268_);
lean_dec(v___x_1273_);
if (v___x_1274_ == 0)
{
if (v_pOpt_1243_ == 0)
{
lean_object* v___x_1275_; lean_object* v_s_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_sz_1266_);
lean_dec(v_pos_1265_);
v___x_1275_ = lean_box(0);
v_s_1276_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1267_, v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1278_ = l_Lean_Parser_ParserState_mkNode(v_s_1276_, v___x_1277_, v_iniSz_1242_);
return v___x_1278_;
}
else
{
lean_object* v_s_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_s_1279_ = l_Lean_Parser_ParserState_restore(v_s_1267_, v_sz_1266_, v_pos_1265_);
lean_dec(v_sz_1266_);
v___x_1280_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1281_ = l_Lean_Parser_ParserState_mkNode(v_s_1279_, v___x_1280_, v_iniSz_1242_);
return v___x_1281_;
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec(v_sz_1266_);
lean_dec(v_pos_1265_);
v___x_1282_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1283_ = l_Lean_Parser_ParserState_mkNode(v_s_1267_, v___x_1282_, v_iniSz_1242_);
return v___x_1283_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
lean_dec(v_pos_1265_);
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_nat_add(v_sz_1266_, v___x_1284_);
v___x_1286_ = l_Lean_Parser_ParserState_stackSize(v_s_1267_);
v___x_1287_ = lean_nat_dec_lt(v___x_1285_, v___x_1286_);
lean_dec(v___x_1286_);
lean_dec(v___x_1285_);
if (v___x_1287_ == 0)
{
lean_dec(v_sz_1266_);
v_s_1247_ = v_s_1267_;
v_pos_1248_ = v_pos_1268_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1288_; lean_object* v_s_1289_; lean_object* v_pos_1290_; 
lean_dec(v_pos_1268_);
v___x_1288_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1289_ = l_Lean_Parser_ParserState_mkNode(v_s_1267_, v___x_1288_, v_sz_1266_);
lean_dec(v_sz_1266_);
v_pos_1290_ = lean_ctor_get(v_s_1289_, 2);
lean_inc(v_pos_1290_);
v_s_1247_ = v_s_1289_;
v_pos_1248_ = v_pos_1290_;
goto v___jp_1246_;
}
}
v___jp_1246_:
{
lean_object* v_sz_1249_; lean_object* v_s_1250_; lean_object* v_errorMsg_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_sz_1249_ = l_Lean_Parser_ParserState_stackSize(v_s_1247_);
lean_inc_ref(v_sep_1240_);
lean_inc_ref(v_c_1244_);
v_s_1250_ = lean_apply_2(v_sep_1240_, v_c_1244_, v_s_1247_);
v_errorMsg_1251_ = lean_ctor_get(v_s_1250_, 4);
lean_inc(v_errorMsg_1251_);
v___x_1252_ = lean_box(0);
v___x_1253_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1251_, v___x_1252_);
lean_dec(v_errorMsg_1251_);
if (v___x_1253_ == 0)
{
lean_object* v_s_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_c_1244_);
lean_dec_ref(v_sep_1240_);
lean_dec_ref(v_p_1239_);
v_s_1254_ = l_Lean_Parser_ParserState_restore(v_s_1250_, v_sz_1249_, v_pos_1248_);
lean_dec(v_sz_1249_);
v___x_1255_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1256_ = l_Lean_Parser_ParserState_mkNode(v_s_1254_, v___x_1255_, v_iniSz_1242_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
lean_dec(v_pos_1248_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_sz_1249_, v___x_1257_);
v___x_1259_ = l_Lean_Parser_ParserState_stackSize(v_s_1250_);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
lean_dec(v___x_1259_);
lean_dec(v___x_1258_);
if (v___x_1260_ == 0)
{
lean_dec(v_sz_1249_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1241_;
lean_object* _tmp_6 = v_s_1250_;
v_pOpt_1243_ = _tmp_4;
v_s_1245_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1262_; lean_object* v_s_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1263_ = l_Lean_Parser_ParserState_mkNode(v_s_1250_, v___x_1262_, v_sz_1249_);
lean_dec(v_sz_1249_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1241_;
lean_object* _tmp_6 = v_s_1263_;
v_pOpt_1243_ = _tmp_4;
v_s_1245_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1239_ = stack[0].m_obj;
lean_object* v_sep_1240_ = stack[1].m_obj;
uint8_t v_allowTrailingSep_1241_ = stack[2].m_num;
lean_object* v_iniSz_1242_ = stack[3].m_obj;
uint8_t v_pOpt_1243_ = stack[4].m_num;
lean_object* v_c_1244_ = stack[5].m_obj;
lean_object* v_s_1245_ = stack[6].m_obj;
lean_object* v_res_1291_;
v_res_1291_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1239_, v_sep_1240_, v_allowTrailingSep_1241_, v_iniSz_1242_, v_pOpt_1243_, v_c_1244_, v_s_1245_);
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1292_, lean_object* v_sep_1293_, lean_object* v_allowTrailingSep_1294_, lean_object* v_iniSz_1295_, lean_object* v_pOpt_1296_, lean_object* v_c_1297_, lean_object* v_s_1298_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1299_; uint8_t v_pOpt_boxed_1300_; lean_object* v_res_1301_; 
v_allowTrailingSep_boxed_1299_ = lean_unbox(v_allowTrailingSep_1294_);
v_pOpt_boxed_1300_ = lean_unbox(v_pOpt_1296_);
v_res_1301_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1292_, v_sep_1293_, v_allowTrailingSep_boxed_1299_, v_iniSz_1295_, v_pOpt_boxed_1300_, v_c_1297_, v_s_1298_);
lean_dec(v_iniSz_1295_);
return v_res_1301_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1302_, lean_object* v_sep_1303_, uint8_t v_allowTrailingSep_1304_, lean_object* v_iniSz_1305_, uint8_t v_pOpt_1306_, lean_object* v_c_1307_, lean_object* v_s_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1302_, v_sep_1303_, v_allowTrailingSep_1304_, v_iniSz_1305_, v_pOpt_1306_, v_c_1307_, v_s_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1302_ = stack[0].m_obj;
lean_object* v_sep_1303_ = stack[1].m_obj;
uint8_t v_allowTrailingSep_1304_ = stack[2].m_num;
lean_object* v_iniSz_1305_ = stack[3].m_obj;
uint8_t v_pOpt_1306_ = stack[4].m_num;
lean_object* v_c_1307_ = stack[5].m_obj;
lean_object* v_s_1308_ = stack[6].m_obj;
lean_object* v_res_1310_;
v_res_1310_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1302_, v_sep_1303_, v_allowTrailingSep_1304_, v_iniSz_1305_, v_pOpt_1306_, v_c_1307_, v_s_1308_);
stack->m_obj
 = v_res_1310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1311_, lean_object* v_sep_1312_, lean_object* v_allowTrailingSep_1313_, lean_object* v_iniSz_1314_, lean_object* v_pOpt_1315_, lean_object* v_c_1316_, lean_object* v_s_1317_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1318_; uint8_t v_pOpt_boxed_1319_; lean_object* v_res_1320_; 
v_allowTrailingSep_boxed_1318_ = lean_unbox(v_allowTrailingSep_1313_);
v_pOpt_boxed_1319_ = lean_unbox(v_pOpt_1315_);
v_res_1320_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1311_, v_sep_1312_, v_allowTrailingSep_boxed_1318_, v_iniSz_1314_, v_pOpt_boxed_1319_, v_c_1316_, v_s_1317_);
lean_dec(v_iniSz_1314_);
return v_res_1320_;
}
}
lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1321_, lean_object* v_p_1322_, lean_object* v_sep_1323_, lean_object* v_c_1324_, lean_object* v_s_1325_){
_start:
{
lean_object* v_iniSz_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; 
v_iniSz_1326_ = l_Lean_Parser_ParserState_stackSize(v_s_1325_);
v___x_1327_ = 1;
v___x_1328_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1322_, v_sep_1323_, v_allowTrailingSep_1321_, v_iniSz_1326_, v___x_1327_, v_c_1324_, v_s_1325_);
lean_dec(v_iniSz_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepByFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowTrailingSep_1321_ = stack[0].m_num;
lean_object* v_p_1322_ = stack[1].m_obj;
lean_object* v_sep_1323_ = stack[2].m_obj;
lean_object* v_c_1324_ = stack[3].m_obj;
lean_object* v_s_1325_ = stack[4].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_1321_, v_p_1322_, v_sep_1323_, v_c_1324_, v_s_1325_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1330_, lean_object* v_p_1331_, lean_object* v_sep_1332_, lean_object* v_c_1333_, lean_object* v_s_1334_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1335_; lean_object* v_res_1336_; 
v_allowTrailingSep_boxed_1335_ = lean_unbox(v_allowTrailingSep_1330_);
v_res_1336_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1335_, v_p_1331_, v_sep_1332_, v_c_1333_, v_s_1334_);
return v_res_1336_;
}
}
lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1337_, lean_object* v_p_1338_, lean_object* v_sep_1339_, lean_object* v_c_1340_, lean_object* v_s_1341_){
_start:
{
lean_object* v_iniSz_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; 
v_iniSz_1342_ = l_Lean_Parser_ParserState_stackSize(v_s_1341_);
v___x_1343_ = 0;
v___x_1344_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1338_, v_sep_1339_, v_allowTrailingSep_1337_, v_iniSz_1342_, v___x_1343_, v_c_1340_, v_s_1341_);
lean_dec(v_iniSz_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1Fn_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowTrailingSep_1337_ = stack[0].m_num;
lean_object* v_p_1338_ = stack[1].m_obj;
lean_object* v_sep_1339_ = stack[2].m_obj;
lean_object* v_c_1340_ = stack[3].m_obj;
lean_object* v_s_1341_ = stack[4].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_1337_, v_p_1338_, v_sep_1339_, v_c_1340_, v_s_1341_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1346_, lean_object* v_p_1347_, lean_object* v_sep_1348_, lean_object* v_c_1349_, lean_object* v_s_1350_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1351_; lean_object* v_res_1352_; 
v_allowTrailingSep_boxed_1351_ = lean_unbox(v_allowTrailingSep_1346_);
v_res_1352_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1351_, v_p_1347_, v_sep_1348_, v_c_1349_, v_s_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1353_, lean_object* v_sep_1354_){
_start:
{
lean_object* v_collectTokens_1355_; lean_object* v_collectKinds_1356_; lean_object* v_collectTokens_1357_; lean_object* v_collectKinds_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1368_; 
v_collectTokens_1355_ = lean_ctor_get(v_p_1353_, 0);
lean_inc_ref(v_collectTokens_1355_);
v_collectKinds_1356_ = lean_ctor_get(v_p_1353_, 1);
lean_inc_ref(v_collectKinds_1356_);
lean_dec_ref(v_p_1353_);
v_collectTokens_1357_ = lean_ctor_get(v_sep_1354_, 0);
v_collectKinds_1358_ = lean_ctor_get(v_sep_1354_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_sep_1354_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v_sep_1354_, 2);
lean_dec(v_unused_1369_);
v___x_1360_ = v_sep_1354_;
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_collectKinds_1358_);
lean_inc(v_collectTokens_1357_);
lean_dec(v_sep_1354_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1362_, 0, v_collectKinds_1358_);
lean_closure_set(v___f_1362_, 1, v_collectKinds_1356_);
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1363_, 0, v_collectTokens_1357_);
lean_closure_set(v___f_1363_, 1, v_collectTokens_1355_);
v___x_1364_ = lean_box(1);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 2, v___x_1364_);
lean_ctor_set(v___x_1360_, 1, v___f_1362_);
lean_ctor_set(v___x_1360_, 0, v___f_1363_);
v___x_1366_ = v___x_1360_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___f_1363_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v___f_1362_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1370_, lean_object* v_sep_1371_){
_start:
{
lean_object* v_collectTokens_1372_; lean_object* v_collectKinds_1373_; lean_object* v_firstTokens_1374_; lean_object* v_collectTokens_1375_; lean_object* v_collectKinds_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1385_; 
v_collectTokens_1372_ = lean_ctor_get(v_p_1370_, 0);
lean_inc_ref(v_collectTokens_1372_);
v_collectKinds_1373_ = lean_ctor_get(v_p_1370_, 1);
lean_inc_ref(v_collectKinds_1373_);
v_firstTokens_1374_ = lean_ctor_get(v_p_1370_, 2);
lean_inc(v_firstTokens_1374_);
lean_dec_ref(v_p_1370_);
v_collectTokens_1375_ = lean_ctor_get(v_sep_1371_, 0);
v_collectKinds_1376_ = lean_ctor_get(v_sep_1371_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_sep_1371_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v_sep_1371_, 2);
lean_dec(v_unused_1386_);
v___x_1378_ = v_sep_1371_;
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_collectKinds_1376_);
lean_inc(v_collectTokens_1375_);
lean_dec(v_sep_1371_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1383_; 
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1380_, 0, v_collectKinds_1376_);
lean_closure_set(v___f_1380_, 1, v_collectKinds_1373_);
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1381_, 0, v_collectTokens_1375_);
lean_closure_set(v___f_1381_, 1, v_collectTokens_1372_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 2, v_firstTokens_1374_);
lean_ctor_set(v___x_1378_, 1, v___f_1380_);
lean_ctor_set(v___x_1378_, 0, v___f_1381_);
v___x_1383_ = v___x_1378_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___f_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___f_1380_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_firstTokens_1374_);
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
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1387_, lean_object* v_sep_1388_, uint8_t v_allowTrailingSep_1389_){
_start:
{
lean_object* v_info_1390_; lean_object* v_fn_1391_; lean_object* v_info_1392_; lean_object* v_fn_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1403_; 
v_info_1390_ = lean_ctor_get(v_p_1387_, 0);
lean_inc_ref(v_info_1390_);
v_fn_1391_ = lean_ctor_get(v_p_1387_, 1);
lean_inc_ref(v_fn_1391_);
lean_dec_ref(v_p_1387_);
v_info_1392_ = lean_ctor_get(v_sep_1388_, 0);
v_fn_1393_ = lean_ctor_get(v_sep_1388_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_sep_1388_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1395_ = v_sep_1388_;
v_isShared_1396_ = v_isSharedCheck_1403_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_fn_1393_);
lean_inc(v_info_1392_);
lean_dec(v_sep_1388_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1403_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1397_ = l_Lean_Parser_sepByInfo(v_info_1390_, v_info_1392_);
v___x_1398_ = lean_box(v_allowTrailingSep_1389_);
v___x_1399_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1399_, 0, v___x_1398_);
lean_closure_set(v___x_1399_, 1, v_fn_1391_);
lean_closure_set(v___x_1399_, 2, v_fn_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1399_);
lean_ctor_set(v___x_1395_, 0, v___x_1397_);
v___x_1401_ = v___x_1395_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_sepByNoAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1387_ = stack[0].m_obj;
lean_object* v_sep_1388_ = stack[1].m_obj;
uint8_t v_allowTrailingSep_1389_ = stack[2].m_num;
lean_object* v_res_1404_;
v_res_1404_ = l_Lean_Parser_sepByNoAntiquot(v_p_1387_, v_sep_1388_, v_allowTrailingSep_1389_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1405_, lean_object* v_sep_1406_, lean_object* v_allowTrailingSep_1407_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1408_; lean_object* v_res_1409_; 
v_allowTrailingSep_boxed_1408_ = lean_unbox(v_allowTrailingSep_1407_);
v_res_1409_ = l_Lean_Parser_sepByNoAntiquot(v_p_1405_, v_sep_1406_, v_allowTrailingSep_boxed_1408_);
return v_res_1409_;
}
}
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1410_, lean_object* v_sep_1411_, uint8_t v_allowTrailingSep_1412_){
_start:
{
lean_object* v_info_1413_; lean_object* v_fn_1414_; lean_object* v_info_1415_; lean_object* v_fn_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
v_info_1413_ = lean_ctor_get(v_p_1410_, 0);
lean_inc_ref(v_info_1413_);
v_fn_1414_ = lean_ctor_get(v_p_1410_, 1);
lean_inc_ref(v_fn_1414_);
lean_dec_ref(v_p_1410_);
v_info_1415_ = lean_ctor_get(v_sep_1411_, 0);
v_fn_1416_ = lean_ctor_get(v_sep_1411_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_sep_1411_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1418_ = v_sep_1411_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_fn_1416_);
lean_inc(v_info_1415_);
lean_dec(v_sep_1411_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1420_ = l_Lean_Parser_sepBy1Info(v_info_1413_, v_info_1415_);
v___x_1421_ = lean_box(v_allowTrailingSep_1412_);
v___x_1422_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1422_, 0, v___x_1421_);
lean_closure_set(v___x_1422_, 1, v_fn_1414_);
lean_closure_set(v___x_1422_, 2, v_fn_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1422_);
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1424_ = v___x_1418_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1NoAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1410_ = stack[0].m_obj;
lean_object* v_sep_1411_ = stack[1].m_obj;
uint8_t v_allowTrailingSep_1412_ = stack[2].m_num;
lean_object* v_res_1427_;
v_res_1427_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1410_, v_sep_1411_, v_allowTrailingSep_1412_);
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1428_, lean_object* v_sep_1429_, lean_object* v_allowTrailingSep_1430_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1431_; lean_object* v_res_1432_; 
v_allowTrailingSep_boxed_1431_ = lean_unbox(v_allowTrailingSep_1430_);
v_res_1432_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1428_, v_sep_1429_, v_allowTrailingSep_boxed_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1433_, lean_object* v_f_1434_, lean_object* v_c_1435_, lean_object* v_s_1436_){
_start:
{
lean_object* v_s_1437_; lean_object* v_stxStack_1438_; lean_object* v_errorMsg_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_s_1437_ = lean_apply_2(v_p_1433_, v_c_1435_, v_s_1436_);
v_stxStack_1438_ = lean_ctor_get(v_s_1437_, 0);
lean_inc_ref(v_stxStack_1438_);
v_errorMsg_1439_ = lean_ctor_get(v_s_1437_, 4);
lean_inc(v_errorMsg_1439_);
v___x_1440_ = lean_box(0);
v___x_1441_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1439_, v___x_1440_);
lean_dec(v_errorMsg_1439_);
if (v___x_1441_ == 0)
{
lean_dec_ref(v_stxStack_1438_);
lean_dec_ref(v_f_1434_);
return v_s_1437_;
}
else
{
lean_object* v_stx_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_stx_1442_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1438_);
lean_dec_ref(v_stxStack_1438_);
v___x_1443_ = l_Lean_Parser_ParserState_popSyntax(v_s_1437_);
v___x_1444_ = lean_apply_1(v_f_1434_, v_stx_1442_);
v___x_1445_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1443_, v___x_1444_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1446_){
_start:
{
lean_object* v_collectTokens_1447_; lean_object* v_collectKinds_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
v_collectTokens_1447_ = lean_ctor_get(v_p_1446_, 0);
v_collectKinds_1448_ = lean_ctor_get(v_p_1446_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_p_1446_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_p_1446_, 2);
lean_dec(v_unused_1457_);
v___x_1450_ = v_p_1446_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_collectKinds_1448_);
lean_inc(v_collectTokens_1447_);
lean_dec(v_p_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = lean_box(1);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 2, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_collectTokens_1447_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_collectKinds_1448_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1458_, lean_object* v_f_1459_){
_start:
{
lean_object* v_info_1460_; lean_object* v_fn_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1470_; 
v_info_1460_ = lean_ctor_get(v_p_1458_, 0);
v_fn_1461_ = lean_ctor_get(v_p_1458_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_p_1458_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1463_ = v_p_1458_;
v_isShared_1464_ = v_isSharedCheck_1470_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_fn_1461_);
lean_inc(v_info_1460_);
lean_dec(v_p_1458_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1470_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1465_ = l_Lean_Parser_withResultOfInfo(v_info_1460_);
v___x_1466_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1466_, 0, v_fn_1461_);
lean_closure_set(v___x_1466_, 1, v_f_1459_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v___x_1466_);
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1468_ = v___x_1463_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = l_Lean_Syntax_getNumArgs(v_stx_1471_);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_dec_eq(v___x_1472_, v___x_1473_);
lean_dec(v___x_1472_);
if (v___x_1474_ == 0)
{
lean_inc(v_stx_1471_);
return v_stx_1471_;
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = l_Lean_Syntax_getArg(v_stx_1471_, v___x_1475_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1477_);
lean_dec(v_stx_1477_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1480_){
_start:
{
lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___f_1481_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1482_ = l_Lean_Parser_many1NoAntiquot(v_p_1480_);
v___x_1483_ = l_Lean_Parser_withResultOf(v___x_1482_, v___f_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1484_, lean_object* v_errorMsg_1485_, lean_object* v_c_1486_, lean_object* v_s_1487_){
_start:
{
lean_object* v_pos_1488_; lean_object* v_toInputContext_1489_; uint8_t v___x_1490_; 
v_pos_1488_ = lean_ctor_get(v_s_1487_, 2);
v_toInputContext_1489_ = lean_ctor_get(v_c_1486_, 0);
v___x_1490_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1489_, v_pos_1488_);
if (v___x_1490_ == 0)
{
lean_object* v_inputString_1491_; uint32_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_inputString_1491_ = lean_ctor_get(v_toInputContext_1489_, 0);
v___x_1492_ = lean_string_utf8_get_fast(v_inputString_1491_, v_pos_1488_);
v___x_1493_ = lean_box_uint32(v___x_1492_);
v___x_1494_ = lean_apply_1(v_p_1484_, v___x_1493_);
v___x_1495_ = lean_unbox(v___x_1494_);
if (v___x_1495_ == 0)
{
uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = 1;
v___x_1497_ = lean_box(0);
v___x_1498_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1487_, v_errorMsg_1485_, v___x_1497_, v___x_1496_);
return v___x_1498_;
}
else
{
lean_object* v___x_1499_; 
lean_inc(v_pos_1488_);
lean_dec_ref(v_errorMsg_1485_);
v___x_1499_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1487_, v_c_1486_, v_pos_1488_);
lean_dec(v_pos_1488_);
return v___x_1499_;
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_errorMsg_1485_);
lean_dec_ref(v_p_1484_);
v___x_1500_ = lean_box(0);
v___x_1501_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1487_, v___x_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1502_, lean_object* v_errorMsg_1503_, lean_object* v_c_1504_, lean_object* v_s_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Parser_satisfyFn(v_p_1502_, v_errorMsg_1503_, v_c_1504_, v_s_1505_);
lean_dec_ref(v_c_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1507_, lean_object* v_c_1508_, lean_object* v_s_1509_){
_start:
{
lean_object* v_pos_1510_; lean_object* v_toInputContext_1511_; uint8_t v___x_1512_; 
v_pos_1510_ = lean_ctor_get(v_s_1509_, 2);
v_toInputContext_1511_ = lean_ctor_get(v_c_1508_, 0);
v___x_1512_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1511_, v_pos_1510_);
if (v___x_1512_ == 0)
{
lean_object* v_inputString_1513_; uint32_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_inputString_1513_ = lean_ctor_get(v_toInputContext_1511_, 0);
v___x_1514_ = lean_string_utf8_get_fast(v_inputString_1513_, v_pos_1510_);
v___x_1515_ = lean_box_uint32(v___x_1514_);
lean_inc_ref(v_p_1507_);
v___x_1516_ = lean_apply_1(v_p_1507_, v___x_1515_);
v___x_1517_ = lean_unbox(v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_inc(v_pos_1510_);
v___x_1518_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1509_, v_c_1508_, v_pos_1510_);
lean_dec(v_pos_1510_);
v_s_1509_ = v___x_1518_;
goto _start;
}
else
{
lean_dec_ref(v_p_1507_);
return v_s_1509_;
}
}
else
{
lean_dec_ref(v_p_1507_);
return v_s_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1520_, lean_object* v_c_1521_, lean_object* v_s_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Parser_takeUntilFn(v_p_1520_, v_c_1521_, v_s_1522_);
lean_dec_ref(v_c_1521_);
return v_res_1523_;
}
}
uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1524_, uint32_t v_c_1525_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_box_uint32(v_c_1525_);
v___x_1527_ = lean_apply_1(v_p_1524_, v___x_1526_);
v___x_1528_ = lean_unbox(v___x_1527_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = 1;
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = 0;
return v___x_1530_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_takeWhileFn___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1524_ = stack[0].m_obj;
uint32_t v_c_1525_ = stack[1].m_num;
uint8_t v_res_1531_;
v_res_1531_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1524_, v_c_1525_);
stack->m_num = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1532_, lean_object* v_c_1533_){
_start:
{
uint32_t v_c_boxed_1534_; uint8_t v_res_1535_; lean_object* v_r_1536_; 
v_c_boxed_1534_ = lean_unbox_uint32(v_c_1533_);
lean_dec(v_c_1533_);
v_res_1535_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1532_, v_c_boxed_1534_);
v_r_1536_ = lean_box(v_res_1535_);
return v_r_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___f_1540_; lean_object* v___x_1541_; 
v___f_1540_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1540_, 0, v_p_1537_);
v___x_1541_ = l_Lean_Parser_takeUntilFn(v___f_1540_, v_a_1538_, v_a_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Parser_takeWhileFn(v_p_1542_, v_a_1543_, v_a_1544_);
lean_dec_ref(v_a_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1546_, lean_object* v_errorMsg_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_inc_ref(v_p_1546_);
v___x_1550_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1550_, 0, v_p_1546_);
lean_closure_set(v___x_1550_, 1, v_errorMsg_1547_);
v___x_1551_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1551_, 0, v_p_1546_);
v___x_1552_ = l_Lean_Parser_andthenFn(v___x_1550_, v___x_1551_, v_a_1548_, v_a_1549_);
return v___x_1552_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1554_, lean_object* v_s_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1557_ = lean_box(0);
v___x_1558_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1555_, v___x_1556_, v___x_1557_, v_pushMissingOnError_1554_);
return v___x_1558_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi_0interp(lean_interpreter_value* stack)
{
uint8_t v_pushMissingOnError_1554_ = stack[0].m_num;
lean_object* v_s_1555_ = stack[1].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1554_, v_s_1555_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1560_, lean_object* v_s_1561_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1562_; lean_object* v_res_1563_; 
v_pushMissingOnError_boxed_1562_ = lean_unbox(v_pushMissingOnError_1560_);
v_res_1563_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1562_, v_s_1561_);
return v_res_1563_;
}
}
lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1564_, lean_object* v_nesting_1565_, lean_object* v_c_1566_, lean_object* v_s_1567_){
_start:
{
lean_object* v_pos_1568_; lean_object* v_toInputContext_1569_; uint8_t v___x_1570_; 
v_pos_1568_ = lean_ctor_get(v_s_1567_, 2);
v_toInputContext_1569_ = lean_ctor_get(v_c_1566_, 0);
v___x_1570_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1569_, v_pos_1568_);
if (v___x_1570_ == 0)
{
lean_object* v_inputString_1571_; uint32_t v_curr_1572_; lean_object* v_i_1573_; uint32_t v___x_1574_; uint8_t v___x_1575_; 
v_inputString_1571_ = lean_ctor_get(v_toInputContext_1569_, 0);
v_curr_1572_ = lean_string_utf8_get_fast(v_inputString_1571_, v_pos_1568_);
v_i_1573_ = lean_string_utf8_next_fast(v_inputString_1571_, v_pos_1568_);
v___x_1574_ = 45;
v___x_1575_ = lean_uint32_dec_eq(v_curr_1572_, v___x_1574_);
if (v___x_1575_ == 0)
{
uint32_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = 47;
v___x_1577_ = lean_uint32_dec_eq(v_curr_1572_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Parser_ParserState_setPos(v_s_1567_, v_i_1573_);
v_s_1567_ = v___x_1578_;
goto _start;
}
else
{
uint8_t v___x_1580_; 
v___x_1580_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1569_, v_i_1573_);
if (v___x_1580_ == 0)
{
uint32_t v_curr_1581_; uint8_t v___x_1582_; 
v_curr_1581_ = lean_string_utf8_get_fast(v_inputString_1571_, v_i_1573_);
v___x_1582_ = lean_uint32_dec_eq(v_curr_1581_, v___x_1574_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Parser_ParserState_setPos(v_s_1567_, v_i_1573_);
v_s_1567_ = v___x_1583_;
goto _start;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_nat_add(v_nesting_1565_, v___x_1585_);
lean_dec(v_nesting_1565_);
v___x_1587_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1567_, v_c_1566_, v_i_1573_);
v_nesting_1565_ = v___x_1586_;
v_s_1567_ = v___x_1587_;
goto _start;
}
}
else
{
lean_object* v___x_1589_; 
lean_dec(v_nesting_1565_);
v___x_1589_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1564_, v_s_1567_);
return v___x_1589_;
}
}
}
else
{
uint8_t v___x_1590_; 
v___x_1590_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1569_, v_i_1573_);
if (v___x_1590_ == 0)
{
uint32_t v_curr_1591_; uint32_t v___x_1592_; uint8_t v___x_1593_; 
v_curr_1591_ = lean_string_utf8_get_fast(v_inputString_1571_, v_i_1573_);
v___x_1592_ = 47;
v___x_1593_ = lean_uint32_dec_eq(v_curr_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Parser_ParserState_setPos(v_s_1567_, v_i_1573_);
v_s_1567_ = v___x_1594_;
goto _start;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_dec_eq(v_nesting_1565_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_nat_sub(v_nesting_1565_, v___x_1596_);
lean_dec(v_nesting_1565_);
v___x_1599_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1567_, v_c_1566_, v_i_1573_);
v_nesting_1565_ = v___x_1598_;
v_s_1567_ = v___x_1599_;
goto _start;
}
else
{
lean_object* v___x_1601_; 
lean_dec(v_nesting_1565_);
v___x_1601_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1567_, v_c_1566_, v_i_1573_);
return v___x_1601_;
}
}
}
else
{
lean_object* v___x_1602_; 
lean_dec(v_nesting_1565_);
v___x_1602_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1564_, v_s_1567_);
return v___x_1602_;
}
}
}
else
{
lean_object* v___x_1603_; 
lean_dec(v_nesting_1565_);
v___x_1603_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1564_, v_s_1567_);
return v___x_1603_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_finishCommentBlock_0interp(lean_interpreter_value* stack)
{
uint8_t v_pushMissingOnError_1564_ = stack[0].m_num;
lean_object* v_nesting_1565_ = stack[1].m_obj;
lean_object* v_c_1566_ = stack[2].m_obj;
lean_object* v_s_1567_ = stack[3].m_obj;
lean_object* v_res_1604_;
v_res_1604_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_1564_, v_nesting_1565_, v_c_1566_, v_s_1567_);
stack->m_obj
 = v_res_1604_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1605_, lean_object* v_nesting_1606_, lean_object* v_c_1607_, lean_object* v_s_1608_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1609_; lean_object* v_res_1610_; 
v_pushMissingOnError_boxed_1609_ = lean_unbox(v_pushMissingOnError_1605_);
v_res_1610_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1609_, v_nesting_1606_, v_c_1607_, v_s_1608_);
lean_dec_ref(v_c_1607_);
return v_res_1610_;
}
}
uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1611_){
_start:
{
uint32_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = 10;
v___x_1613_ = lean_uint32_dec_eq(v_c_1611_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT void l_Lean_Parser_whitespace___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1611_ = stack[0].m_num;
uint8_t v_res_1614_;
v_res_1614_ = l_Lean_Parser_whitespace___lam__0(v_c_1611_);
stack->m_num = v_res_1614_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1615_){
_start:
{
uint32_t v_c_boxed_1616_; uint8_t v_res_1617_; lean_object* v_r_1618_; 
v_c_boxed_1616_ = lean_unbox_uint32(v_c_1615_);
lean_dec(v_c_1615_);
v_res_1617_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1616_);
v_r_1618_ = lean_box(v_res_1617_);
return v_r_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1624_, lean_object* v_s_1625_){
_start:
{
lean_object* v_pos_1626_; lean_object* v_toInputContext_1630_; uint8_t v___x_1631_; 
v_pos_1626_ = lean_ctor_get(v_s_1625_, 2);
v_toInputContext_1630_ = lean_ctor_get(v_c_1624_, 0);
v___x_1631_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1630_, v_pos_1626_);
if (v___x_1631_ == 0)
{
lean_object* v_inputString_1632_; uint32_t v_curr_1633_; uint32_t v___x_1634_; uint8_t v___x_1635_; 
v_inputString_1632_ = lean_ctor_get(v_toInputContext_1630_, 0);
v_curr_1633_ = lean_string_utf8_get_fast(v_inputString_1632_, v_pos_1626_);
v___x_1634_ = 9;
v___x_1635_ = lean_uint32_dec_eq(v_curr_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
uint32_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = 13;
v___x_1637_ = lean_uint32_dec_eq(v_curr_1633_, v___x_1636_);
if (v___x_1637_ == 0)
{
uint32_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = 32;
v___x_1639_ = lean_uint32_dec_eq(v_curr_1633_, v___x_1638_);
if (v___x_1639_ == 0)
{
if (v___x_1635_ == 0)
{
if (v___x_1637_ == 0)
{
uint32_t v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = 10;
v___x_1641_ = lean_uint32_dec_eq(v_curr_1633_, v___x_1640_);
if (v___x_1641_ == 0)
{
uint32_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = 45;
v___x_1643_ = lean_uint32_dec_eq(v_curr_1633_, v___x_1642_);
if (v___x_1643_ == 0)
{
uint32_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = 47;
v___x_1645_ = lean_uint32_dec_eq(v_curr_1633_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_dec_ref(v_c_1624_);
return v_s_1625_;
}
else
{
lean_object* v_i_1646_; uint32_t v_curr_1647_; uint8_t v___x_1648_; 
v_i_1646_ = lean_string_utf8_next_fast(v_inputString_1632_, v_pos_1626_);
v_curr_1647_ = lean_string_utf8_get(v_inputString_1632_, v_i_1646_);
v___x_1648_ = lean_uint32_dec_eq(v_curr_1647_, v___x_1642_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v_c_1624_);
return v_s_1625_;
}
else
{
lean_object* v_i_1649_; uint32_t v_curr_1650_; uint8_t v___x_1651_; 
v_i_1649_ = lean_string_utf8_next(v_inputString_1632_, v_i_1646_);
v_curr_1650_ = lean_string_utf8_get(v_inputString_1632_, v_i_1649_);
v___x_1651_ = lean_uint32_dec_eq(v_curr_1650_, v___x_1642_);
if (v___x_1651_ == 0)
{
uint32_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = 33;
v___x_1653_ = lean_uint32_dec_eq(v_curr_1650_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_box(v___x_1653_);
v___x_1656_ = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(v___x_1656_, 0, v___x_1655_);
lean_closure_set(v___x_1656_, 1, v___x_1654_);
v___x_1657_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1658_ = l_Lean_Parser_ParserState_next(v_s_1625_, v_c_1624_, v_i_1649_);
lean_dec(v_i_1649_);
v___x_1659_ = l_Lean_Parser_andthenFn(v___x_1656_, v___x_1657_, v_c_1624_, v___x_1658_);
return v___x_1659_;
}
else
{
lean_dec(v_i_1649_);
lean_dec_ref(v_c_1624_);
return v_s_1625_;
}
}
else
{
lean_dec(v_i_1649_);
lean_dec_ref(v_c_1624_);
return v_s_1625_;
}
}
}
}
else
{
lean_object* v_i_1660_; uint32_t v_curr_1661_; uint8_t v___x_1662_; 
v_i_1660_ = lean_string_utf8_next_fast(v_inputString_1632_, v_pos_1626_);
v_curr_1661_ = lean_string_utf8_get(v_inputString_1632_, v_i_1660_);
v___x_1662_ = lean_uint32_dec_eq(v_curr_1661_, v___x_1642_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_c_1624_);
return v_s_1625_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1664_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1665_ = l_Lean_Parser_ParserState_next(v_s_1625_, v_c_1624_, v_i_1660_);
v___x_1666_ = l_Lean_Parser_andthenFn(v___x_1663_, v___x_1664_, v_c_1624_, v___x_1665_);
return v___x_1666_;
}
}
}
else
{
lean_inc(v_pos_1626_);
goto v___jp_1627_;
}
}
else
{
lean_inc(v_pos_1626_);
goto v___jp_1627_;
}
}
else
{
lean_inc(v_pos_1626_);
goto v___jp_1627_;
}
}
else
{
lean_inc(v_pos_1626_);
goto v___jp_1627_;
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v_c_1624_);
v___x_1667_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1668_ = lean_box(0);
v___x_1669_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1625_, v___x_1667_, v___x_1668_, v___x_1635_);
return v___x_1669_;
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec_ref(v_c_1624_);
v___x_1670_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1625_, v___x_1670_, v___x_1671_, v___x_1631_);
return v___x_1672_;
}
}
else
{
lean_dec_ref(v_c_1624_);
return v_s_1625_;
}
v___jp_1627_:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1625_, v_c_1624_, v_pos_1626_);
lean_dec(v_pos_1626_);
v_s_1625_ = v___x_1628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1673_, lean_object* v_p_1674_){
_start:
{
lean_object* v_toInputContext_1675_; lean_object* v_inputString_1676_; lean_object* v_endPos_1677_; uint8_t v___x_1678_; 
v_toInputContext_1675_ = lean_ctor_get(v_c_1673_, 0);
v_inputString_1676_ = lean_ctor_get(v_toInputContext_1675_, 0);
v_endPos_1677_ = lean_ctor_get(v_toInputContext_1675_, 3);
v___x_1678_ = lean_nat_dec_le(v_p_1674_, v_endPos_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_inc(v_endPos_1677_);
lean_inc_ref(v_inputString_1676_);
v___x_1679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1679_, 0, v_inputString_1676_);
lean_ctor_set(v___x_1679_, 1, v_p_1674_);
lean_ctor_set(v___x_1679_, 2, v_endPos_1677_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; 
lean_inc(v_p_1674_);
lean_inc_ref(v_inputString_1676_);
v___x_1680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1680_, 0, v_inputString_1676_);
lean_ctor_set(v___x_1680_, 1, v_p_1674_);
lean_ctor_set(v___x_1680_, 2, v_p_1674_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1681_, lean_object* v_p_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1681_, v_p_1682_);
lean_dec_ref(v_c_1681_);
return v_res_1683_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1684_, uint8_t v_trailingWs_1685_, lean_object* v_c_1686_, lean_object* v_s_1687_){
_start:
{
lean_object* v_toInputContext_1688_; lean_object* v_pos_1689_; lean_object* v_inputString_1690_; lean_object* v_endPos_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1719_; 
v_toInputContext_1688_ = lean_ctor_get(v_c_1686_, 0);
lean_inc_ref(v_toInputContext_1688_);
v_pos_1689_ = lean_ctor_get(v_s_1687_, 2);
v_inputString_1690_ = lean_ctor_get(v_toInputContext_1688_, 0);
v_endPos_1691_ = lean_ctor_get(v_toInputContext_1688_, 3);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_toInputContext_1688_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1720_ = lean_ctor_get(v_toInputContext_1688_, 2);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_toInputContext_1688_, 1);
lean_dec(v_unused_1721_);
v___x_1693_ = v_toInputContext_1688_;
v_isShared_1694_ = v_isSharedCheck_1719_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_endPos_1691_);
lean_inc(v_inputString_1690_);
lean_dec(v_toInputContext_1688_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1719_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_leading_1695_; lean_object* v_val_1696_; 
lean_inc(v_startPos_1684_);
v_leading_1695_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1686_, v_startPos_1684_);
v_val_1696_ = lean_string_utf8_extract(v_inputString_1690_, v_startPos_1684_, v_pos_1689_);
if (v_trailingWs_1685_ == 0)
{
lean_object* v_trailing_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec(v_endPos_1691_);
lean_dec_ref(v_inputString_1690_);
lean_inc(v_pos_1689_);
v_trailing_1697_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1686_, v_pos_1689_);
lean_dec_ref(v_c_1686_);
v___x_1698_ = lean_string_utf8_byte_size(v_val_1696_);
v___x_1699_ = lean_nat_add(v_startPos_1684_, v___x_1698_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 3, v___x_1699_);
lean_ctor_set(v___x_1693_, 2, v_trailing_1697_);
lean_ctor_set(v___x_1693_, 1, v_startPos_1684_);
lean_ctor_set(v___x_1693_, 0, v_leading_1695_);
v___x_1701_ = v___x_1693_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_leading_1695_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_startPos_1684_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_trailing_1697_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v_atom_1702_; lean_object* v___x_1703_; 
v_atom_1702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1702_, 0, v___x_1701_);
lean_ctor_set(v_atom_1702_, 1, v_val_1696_);
v___x_1703_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1687_, v_atom_1702_);
return v___x_1703_;
}
}
else
{
lean_object* v_s_1705_; lean_object* v___y_1707_; lean_object* v_pos_1715_; uint8_t v___x_1716_; 
lean_inc(v_pos_1689_);
v_s_1705_ = l_Lean_Parser_whitespace(v_c_1686_, v_s_1687_);
v_pos_1715_ = lean_ctor_get(v_s_1705_, 2);
v___x_1716_ = lean_nat_dec_le(v_pos_1715_, v_endPos_1691_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1717_, 0, v_inputString_1690_);
lean_ctor_set(v___x_1717_, 1, v_pos_1689_);
lean_ctor_set(v___x_1717_, 2, v_endPos_1691_);
v___y_1707_ = v___x_1717_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_endPos_1691_);
lean_inc(v_pos_1715_);
v___x_1718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1718_, 0, v_inputString_1690_);
lean_ctor_set(v___x_1718_, 1, v_pos_1689_);
lean_ctor_set(v___x_1718_, 2, v_pos_1715_);
v___y_1707_ = v___x_1718_;
goto v___jp_1706_;
}
v___jp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1708_ = lean_string_utf8_byte_size(v_val_1696_);
v___x_1709_ = lean_nat_add(v_startPos_1684_, v___x_1708_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 3, v___x_1709_);
lean_ctor_set(v___x_1693_, 2, v___y_1707_);
lean_ctor_set(v___x_1693_, 1, v_startPos_1684_);
lean_ctor_set(v___x_1693_, 0, v_leading_1695_);
v___x_1711_ = v___x_1693_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_leading_1695_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_startPos_1684_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___y_1707_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v_atom_1712_; lean_object* v___x_1713_; 
v_atom_1712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1712_, 0, v___x_1711_);
lean_ctor_set(v_atom_1712_, 1, v_val_1696_);
v___x_1713_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1705_, v_atom_1712_);
return v___x_1713_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_1684_ = stack[0].m_obj;
uint8_t v_trailingWs_1685_ = stack[1].m_num;
lean_object* v_c_1686_ = stack[2].m_obj;
lean_object* v_s_1687_ = stack[3].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1684_, v_trailingWs_1685_, v_c_1686_, v_s_1687_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1723_, lean_object* v_trailingWs_1724_, lean_object* v_c_1725_, lean_object* v_s_1726_){
_start:
{
uint8_t v_trailingWs_boxed_1727_; lean_object* v_res_1728_; 
v_trailingWs_boxed_1727_ = lean_unbox(v_trailingWs_1724_);
v_res_1728_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1723_, v_trailingWs_boxed_1727_, v_c_1725_, v_s_1726_);
return v_res_1728_;
}
}
lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1729_, uint8_t v_trailingWs_1730_, lean_object* v_c_1731_, lean_object* v_s_1732_){
_start:
{
lean_object* v_pos_1733_; lean_object* v_s_1734_; lean_object* v_errorMsg_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_pos_1733_ = lean_ctor_get(v_s_1732_, 2);
lean_inc(v_pos_1733_);
lean_inc_ref(v_c_1731_);
v_s_1734_ = lean_apply_2(v_p_1729_, v_c_1731_, v_s_1732_);
v_errorMsg_1735_ = lean_ctor_get(v_s_1734_, 4);
lean_inc(v_errorMsg_1735_);
v___x_1736_ = lean_box(0);
v___x_1737_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1735_, v___x_1736_);
lean_dec(v_errorMsg_1735_);
if (v___x_1737_ == 0)
{
lean_dec(v_pos_1733_);
lean_dec_ref(v_c_1731_);
return v_s_1734_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1733_, v_trailingWs_1730_, v_c_1731_, v_s_1734_);
return v___x_1738_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_rawFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1729_ = stack[0].m_obj;
uint8_t v_trailingWs_1730_ = stack[1].m_num;
lean_object* v_c_1731_ = stack[2].m_obj;
lean_object* v_s_1732_ = stack[3].m_obj;
lean_object* v_res_1739_;
v_res_1739_ = l_Lean_Parser_rawFn(v_p_1729_, v_trailingWs_1730_, v_c_1731_, v_s_1732_);
stack->m_obj
 = v_res_1739_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1740_, lean_object* v_trailingWs_1741_, lean_object* v_c_1742_, lean_object* v_s_1743_){
_start:
{
uint8_t v_trailingWs_boxed_1744_; lean_object* v_res_1745_; 
v_trailingWs_boxed_1744_ = lean_unbox(v_trailingWs_1741_);
v_res_1745_ = l_Lean_Parser_rawFn(v_p_1740_, v_trailingWs_boxed_1744_, v_c_1742_, v_s_1743_);
return v_res_1745_;
}
}
uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1746_, uint32_t v_d_1747_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_uint32_dec_eq(v_c_1746_, v_d_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT void l_Lean_Parser_chFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1746_ = stack[0].m_num;
uint32_t v_d_1747_ = stack[1].m_num;
uint8_t v_res_1749_;
v_res_1749_ = l_Lean_Parser_chFn___lam__0(v_c_1746_, v_d_1747_);
stack->m_num = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1750_, lean_object* v_d_1751_){
_start:
{
uint32_t v_c_boxed_1752_; uint32_t v_d_boxed_1753_; uint8_t v_res_1754_; lean_object* v_r_1755_; 
v_c_boxed_1752_ = lean_unbox_uint32(v_c_1750_);
lean_dec(v_c_1750_);
v_d_boxed_1753_ = lean_unbox_uint32(v_d_1751_);
lean_dec(v_d_1751_);
v_res_1754_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1752_, v_d_boxed_1753_);
v_r_1755_ = lean_box(v_res_1754_);
return v_r_1755_;
}
}
lean_object* l_Lean_Parser_chFn(uint32_t v_c_1758_, uint8_t v_trailingWs_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1762_ = lean_box_uint32(v_c_1758_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1763_, 0, v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1765_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1766_ = lean_string_push(v___x_1765_, v_c_1758_);
v___x_1767_ = lean_string_append(v___x_1764_, v___x_1766_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = lean_string_append(v___x_1767_, v___x_1764_);
v___x_1769_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1769_, 0, v___f_1763_);
lean_closure_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_Parser_rawFn(v___x_1769_, v_trailingWs_1759_, v_a_1760_, v_a_1761_);
return v___x_1770_;
}
}
LEAN_EXPORT void l_Lean_Parser_chFn_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1758_ = stack[0].m_num;
uint8_t v_trailingWs_1759_ = stack[1].m_num;
lean_object* v_a_1760_ = stack[2].m_obj;
lean_object* v_a_1761_ = stack[3].m_obj;
lean_object* v_res_1771_;
v_res_1771_ = l_Lean_Parser_chFn(v_c_1758_, v_trailingWs_1759_, v_a_1760_, v_a_1761_);
stack->m_obj
 = v_res_1771_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1772_, lean_object* v_trailingWs_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
uint32_t v_c_boxed_1776_; uint8_t v_trailingWs_boxed_1777_; lean_object* v_res_1778_; 
v_c_boxed_1776_ = lean_unbox_uint32(v_c_1772_);
lean_dec(v_c_1772_);
v_trailingWs_boxed_1777_ = lean_unbox(v_trailingWs_1773_);
v_res_1778_ = l_Lean_Parser_chFn(v_c_boxed_1776_, v_trailingWs_boxed_1777_, v_a_1774_, v_a_1775_);
return v_res_1778_;
}
}
lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1779_, uint8_t v_trailingWs_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1782_ = lean_box_uint32(v_c_1779_);
v___x_1783_ = lean_box(v_trailingWs_1780_);
v___x_1784_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1784_, 0, v___x_1782_);
lean_closure_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1781_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT void l_Lean_Parser_rawCh_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1779_ = stack[0].m_num;
uint8_t v_trailingWs_1780_ = stack[1].m_num;
lean_object* v_res_1786_;
v_res_1786_ = l_Lean_Parser_rawCh(v_c_1779_, v_trailingWs_1780_);
stack->m_obj
 = v_res_1786_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1787_, lean_object* v_trailingWs_1788_){
_start:
{
uint32_t v_c_boxed_1789_; uint8_t v_trailingWs_boxed_1790_; lean_object* v_res_1791_; 
v_c_boxed_1789_ = lean_unbox_uint32(v_c_1787_);
lean_dec(v_c_1787_);
v_trailingWs_boxed_1790_ = lean_unbox(v_trailingWs_1788_);
v_res_1791_ = l_Lean_Parser_rawCh(v_c_boxed_1789_, v_trailingWs_boxed_1790_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1793_, lean_object* v_s_1794_){
_start:
{
lean_object* v_pos_1795_; lean_object* v_toInputContext_1796_; uint8_t v___x_1797_; 
v_pos_1795_ = lean_ctor_get(v_s_1794_, 2);
v_toInputContext_1796_ = lean_ctor_get(v_c_1793_, 0);
v___x_1797_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1796_, v_pos_1795_);
if (v___x_1797_ == 0)
{
lean_object* v_inputString_1798_; uint8_t v___x_1799_; uint32_t v_curr_1800_; lean_object* v_i_1801_; uint8_t v___y_1803_; uint8_t v___y_1809_; uint32_t v___x_1820_; uint8_t v___x_1821_; 
v_inputString_1798_ = lean_ctor_get(v_toInputContext_1796_, 0);
v___x_1799_ = 1;
v_curr_1800_ = lean_string_utf8_get_fast(v_inputString_1798_, v_pos_1795_);
v_i_1801_ = lean_string_utf8_next_fast(v_inputString_1798_, v_pos_1795_);
v___x_1820_ = 48;
v___x_1821_ = lean_uint32_dec_le(v___x_1820_, v_curr_1800_);
if (v___x_1821_ == 0)
{
goto v___jp_1815_;
}
else
{
uint32_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = 57;
v___x_1823_ = lean_uint32_dec_le(v_curr_1800_, v___x_1822_);
if (v___x_1823_ == 0)
{
goto v___jp_1815_;
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_Parser_ParserState_setPos(v_s_1794_, v_i_1801_);
return v___x_1824_;
}
}
v___jp_1802_:
{
if (v___y_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1805_ = lean_box(0);
v___x_1806_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1794_, v___x_1804_, v___x_1805_, v___x_1799_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Parser_ParserState_setPos(v_s_1794_, v_i_1801_);
return v___x_1807_;
}
}
v___jp_1808_:
{
if (v___y_1809_ == 0)
{
uint32_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = 65;
v___x_1811_ = lean_uint32_dec_le(v___x_1810_, v_curr_1800_);
if (v___x_1811_ == 0)
{
v___y_1803_ = v___x_1797_;
goto v___jp_1802_;
}
else
{
uint32_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = 70;
v___x_1813_ = lean_uint32_dec_le(v_curr_1800_, v___x_1812_);
v___y_1803_ = v___x_1813_;
goto v___jp_1802_;
}
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_Parser_ParserState_setPos(v_s_1794_, v_i_1801_);
return v___x_1814_;
}
}
v___jp_1815_:
{
uint32_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = 97;
v___x_1817_ = lean_uint32_dec_le(v___x_1816_, v_curr_1800_);
if (v___x_1817_ == 0)
{
v___y_1809_ = v___x_1797_;
goto v___jp_1808_;
}
else
{
uint32_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = 102;
v___x_1819_ = lean_uint32_dec_le(v_curr_1800_, v___x_1818_);
v___y_1809_ = v___x_1819_;
goto v___jp_1808_;
}
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1794_, v___x_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1827_, lean_object* v_s_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Parser_hexDigitFn(v_c_1827_, v_s_1828_);
lean_dec_ref(v_c_1827_);
return v_res_1829_;
}
}
lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1832_, lean_object* v_c_1833_, lean_object* v_s_1834_){
_start:
{
lean_object* v_pos_1835_; lean_object* v_toInputContext_1839_; uint8_t v___x_1840_; 
v_pos_1835_ = lean_ctor_get(v_s_1834_, 2);
v_toInputContext_1839_ = lean_ctor_get(v_c_1833_, 0);
v___x_1840_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1839_, v_pos_1835_);
if (v___x_1840_ == 0)
{
lean_object* v_inputString_1841_; uint8_t v___x_1842_; uint32_t v_curr_1843_; uint32_t v___x_1844_; uint8_t v___x_1845_; 
v_inputString_1841_ = lean_ctor_get(v_toInputContext_1839_, 0);
v___x_1842_ = 1;
v_curr_1843_ = lean_string_utf8_get_fast(v_inputString_1841_, v_pos_1835_);
v___x_1844_ = 10;
v___x_1845_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
uint32_t v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = 32;
v___x_1847_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1846_);
if (v___x_1847_ == 0)
{
uint32_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = 9;
v___x_1849_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1848_);
if (v___x_1849_ == 0)
{
uint32_t v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = 13;
v___x_1851_ = lean_uint32_dec_eq(v_curr_1843_, v___x_1850_);
if (v___x_1851_ == 0)
{
if (v___x_1845_ == 0)
{
if (v_seenNewline_1832_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1853_ = lean_box(0);
v___x_1854_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1834_, v___x_1852_, v___x_1853_, v___x_1842_);
return v___x_1854_;
}
else
{
return v_s_1834_;
}
}
else
{
lean_inc(v_pos_1835_);
goto v___jp_1836_;
}
}
else
{
lean_inc(v_pos_1835_);
goto v___jp_1836_;
}
}
else
{
lean_inc(v_pos_1835_);
goto v___jp_1836_;
}
}
else
{
lean_inc(v_pos_1835_);
goto v___jp_1836_;
}
}
else
{
if (v_seenNewline_1832_ == 0)
{
lean_object* v___x_1855_; 
lean_inc(v_pos_1835_);
v___x_1855_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1834_, v_c_1833_, v_pos_1835_);
lean_dec(v_pos_1835_);
v_seenNewline_1832_ = v___x_1842_;
v_s_1834_ = v___x_1855_;
goto _start;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1858_ = lean_box(0);
v___x_1859_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1834_, v___x_1857_, v___x_1858_, v___x_1842_);
return v___x_1859_;
}
}
}
else
{
return v_s_1834_;
}
v___jp_1836_:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1834_, v_c_1833_, v_pos_1835_);
lean_dec(v_pos_1835_);
v_s_1834_ = v___x_1837_;
goto _start;
}
}
}
LEAN_EXPORT void l_Lean_Parser_stringGapFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_seenNewline_1832_ = stack[0].m_num;
lean_object* v_c_1833_ = stack[1].m_obj;
lean_object* v_s_1834_ = stack[2].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_Lean_Parser_stringGapFn(v_seenNewline_1832_, v_c_1833_, v_s_1834_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1861_, lean_object* v_c_1862_, lean_object* v_s_1863_){
_start:
{
uint8_t v_seenNewline_boxed_1864_; lean_object* v_res_1865_; 
v_seenNewline_boxed_1864_ = lean_unbox(v_seenNewline_1861_);
v_res_1865_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1864_, v_c_1862_, v_s_1863_);
lean_dec_ref(v_c_1862_);
return v_res_1865_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1867_);
v___x_1868_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1868_, 0, v___x_1867_);
lean_closure_set(v___x_1868_, 1, v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1870_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1871_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1871_, 0, v___x_1870_);
lean_closure_set(v___x_1871_, 1, v___x_1869_);
return v___x_1871_;
}
}
lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1872_, uint8_t v_inString_1873_, lean_object* v_c_1874_, lean_object* v_s_1875_){
_start:
{
lean_object* v_pos_1876_; lean_object* v_toInputContext_1877_; uint8_t v___x_1878_; 
v_pos_1876_ = lean_ctor_get(v_s_1875_, 2);
v_toInputContext_1877_ = lean_ctor_get(v_c_1874_, 0);
v___x_1878_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1877_, v_pos_1876_);
if (v___x_1878_ == 0)
{
lean_object* v_inputString_1879_; uint32_t v_curr_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_inputString_1879_ = lean_ctor_get(v_toInputContext_1877_, 0);
v_curr_1880_ = lean_string_utf8_get_fast(v_inputString_1879_, v_pos_1876_);
v___x_1881_ = lean_box_uint32(v_curr_1880_);
v___x_1882_ = lean_apply_1(v_isQuotable_1872_, v___x_1881_);
v___x_1883_ = lean_unbox(v___x_1882_);
if (v___x_1883_ == 0)
{
uint32_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = 120;
v___x_1885_ = lean_uint32_dec_eq(v_curr_1880_, v___x_1884_);
if (v___x_1885_ == 0)
{
uint32_t v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = 117;
v___x_1887_ = lean_uint32_dec_eq(v_curr_1880_, v___x_1886_);
if (v___x_1887_ == 0)
{
uint8_t v___x_1888_; 
v___x_1888_ = 1;
if (v_inString_1873_ == 0)
{
lean_dec_ref(v_c_1874_);
goto v___jp_1889_;
}
else
{
uint32_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = 10;
v___x_1894_ = lean_uint32_dec_eq(v_curr_1880_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_dec_ref(v_c_1874_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Parser_stringGapFn(v___x_1887_, v_c_1874_, v_s_1875_);
lean_dec_ref(v_c_1874_);
return v___x_1895_;
}
}
v___jp_1889_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1891_ = lean_box(0);
v___x_1892_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1875_, v___x_1890_, v___x_1891_, v___x_1888_);
return v___x_1892_;
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_inc(v_pos_1876_);
v___x_1896_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1897_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1898_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1875_, v_c_1874_, v_pos_1876_);
lean_dec(v_pos_1876_);
v___x_1899_ = l_Lean_Parser_andthenFn(v___x_1896_, v___x_1897_, v_c_1874_, v___x_1898_);
return v___x_1899_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_inc(v_pos_1876_);
v___x_1900_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1901_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1875_, v_c_1874_, v_pos_1876_);
lean_dec(v_pos_1876_);
lean_inc_ref(v___x_1900_);
v___x_1902_ = l_Lean_Parser_andthenFn(v___x_1900_, v___x_1900_, v_c_1874_, v___x_1901_);
return v___x_1902_;
}
}
else
{
lean_object* v___x_1903_; 
lean_inc(v_pos_1876_);
v___x_1903_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1875_, v_c_1874_, v_pos_1876_);
lean_dec(v_pos_1876_);
lean_dec_ref(v_c_1874_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref(v_c_1874_);
lean_dec_ref(v_isQuotable_1872_);
v___x_1904_ = lean_box(0);
v___x_1905_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1875_, v___x_1904_);
return v___x_1905_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_quotedCharCoreFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_isQuotable_1872_ = stack[0].m_obj;
uint8_t v_inString_1873_ = stack[1].m_num;
lean_object* v_c_1874_ = stack[2].m_obj;
lean_object* v_s_1875_ = stack[3].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1872_, v_inString_1873_, v_c_1874_, v_s_1875_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1907_, lean_object* v_inString_1908_, lean_object* v_c_1909_, lean_object* v_s_1910_){
_start:
{
uint8_t v_inString_boxed_1911_; lean_object* v_res_1912_; 
v_inString_boxed_1911_ = lean_unbox(v_inString_1908_);
v_res_1912_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1907_, v_inString_boxed_1911_, v_c_1909_, v_s_1910_);
return v_res_1912_;
}
}
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1913_){
_start:
{
uint32_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = 92;
v___x_1915_ = lean_uint32_dec_eq(v_c_1913_, v___x_1914_);
if (v___x_1915_ == 0)
{
uint32_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = 34;
v___x_1917_ = lean_uint32_dec_eq(v_c_1913_, v___x_1916_);
if (v___x_1917_ == 0)
{
uint32_t v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = 39;
v___x_1919_ = lean_uint32_dec_eq(v_c_1913_, v___x_1918_);
if (v___x_1919_ == 0)
{
uint32_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = 114;
v___x_1921_ = lean_uint32_dec_eq(v_c_1913_, v___x_1920_);
if (v___x_1921_ == 0)
{
uint32_t v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = 110;
v___x_1923_ = lean_uint32_dec_eq(v_c_1913_, v___x_1922_);
if (v___x_1923_ == 0)
{
uint32_t v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = 116;
v___x_1925_ = lean_uint32_dec_eq(v_c_1913_, v___x_1924_);
return v___x_1925_;
}
else
{
return v___x_1923_;
}
}
else
{
return v___x_1921_;
}
}
else
{
return v___x_1919_;
}
}
else
{
return v___x_1917_;
}
}
else
{
return v___x_1915_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_isQuotableCharDefault_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1913_ = stack[0].m_num;
uint8_t v_res_1926_;
v_res_1926_ = l_Lean_Parser_isQuotableCharDefault(v_c_1913_);
stack->m_num = v_res_1926_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1927_){
_start:
{
uint32_t v_c_boxed_1928_; uint8_t v_res_1929_; lean_object* v_r_1930_; 
v_c_boxed_1928_ = lean_unbox_uint32(v_c_1927_);
lean_dec(v_c_1927_);
v_res_1929_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1928_);
v_r_1930_ = lean_box(v_res_1929_);
return v_r_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1935_ = 0;
v___x_1936_ = l_Lean_Parser_quotedCharCoreFn(v___x_1934_, v___x_1935_, v_a_1932_, v_a_1933_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1940_ = 1;
v___x_1941_ = l_Lean_Parser_quotedCharCoreFn(v___x_1939_, v___x_1940_, v_a_1937_, v_a_1938_);
return v___x_1941_;
}
}
lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1942_, lean_object* v_startPos_1943_, uint8_t v_includeWhitespace_1944_, lean_object* v_c_1945_, lean_object* v_s_1946_){
_start:
{
lean_object* v_pos_1947_; lean_object* v_errorMsg_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v_pos_1947_ = lean_ctor_get(v_s_1946_, 2);
v_errorMsg_1948_ = lean_ctor_get(v_s_1946_, 4);
v___x_1949_ = lean_box(0);
v___x_1950_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_dec_ref(v_c_1945_);
lean_dec(v_startPos_1943_);
lean_dec(v_n_1942_);
return v_s_1946_;
}
else
{
lean_object* v_toInputContext_1951_; lean_object* v_inputString_1952_; lean_object* v_endPos_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1975_; 
lean_inc(v_pos_1947_);
v_toInputContext_1951_ = lean_ctor_get(v_c_1945_, 0);
lean_inc_ref(v_toInputContext_1951_);
v_inputString_1952_ = lean_ctor_get(v_toInputContext_1951_, 0);
v_endPos_1953_ = lean_ctor_get(v_toInputContext_1951_, 3);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_toInputContext_1951_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1976_ = lean_ctor_get(v_toInputContext_1951_, 2);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_toInputContext_1951_, 1);
lean_dec(v_unused_1977_);
v___x_1955_ = v_toInputContext_1951_;
v_isShared_1956_ = v_isSharedCheck_1975_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_endPos_1953_);
lean_inc(v_inputString_1952_);
lean_dec(v_toInputContext_1951_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1975_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v_leading_1957_; lean_object* v_val_1958_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1968_; lean_object* v_pos_1969_; 
lean_inc(v_startPos_1943_);
v_leading_1957_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1945_, v_startPos_1943_);
v_val_1958_ = lean_string_utf8_extract(v_inputString_1952_, v_startPos_1943_, v_pos_1947_);
if (v_includeWhitespace_1944_ == 0)
{
lean_dec_ref(v_c_1945_);
lean_inc(v_pos_1947_);
v___y_1968_ = v_s_1946_;
v_pos_1969_ = v_pos_1947_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_1973_; lean_object* v_pos_1974_; 
v___x_1973_ = l_Lean_Parser_whitespace(v_c_1945_, v_s_1946_);
v_pos_1974_ = lean_ctor_get(v___x_1973_, 2);
lean_inc(v_pos_1974_);
v___y_1968_ = v___x_1973_;
v_pos_1969_ = v_pos_1974_;
goto v___jp_1967_;
}
v___jp_1959_:
{
lean_object* v_info_1963_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 3, v_pos_1947_);
lean_ctor_set(v___x_1955_, 2, v___y_1961_);
lean_ctor_set(v___x_1955_, 1, v_startPos_1943_);
lean_ctor_set(v___x_1955_, 0, v_leading_1957_);
v_info_1963_ = v___x_1955_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_leading_1957_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_startPos_1943_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v___y_1961_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_pos_1947_);
v_info_1963_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = l_Lean_Syntax_mkLit(v_n_1942_, v_val_1958_, v_info_1963_);
v___x_1965_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1960_, v___x_1964_);
return v___x_1965_;
}
}
v___jp_1967_:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_le(v_pos_1969_, v_endPos_1953_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec(v_pos_1969_);
lean_inc(v_pos_1947_);
v___x_1971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1971_, 0, v_inputString_1952_);
lean_ctor_set(v___x_1971_, 1, v_pos_1947_);
lean_ctor_set(v___x_1971_, 2, v_endPos_1953_);
v___y_1960_ = v___y_1968_;
v___y_1961_ = v___x_1971_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1972_; 
lean_dec(v_endPos_1953_);
lean_inc(v_pos_1947_);
v___x_1972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1972_, 0, v_inputString_1952_);
lean_ctor_set(v___x_1972_, 1, v_pos_1947_);
lean_ctor_set(v___x_1972_, 2, v_pos_1969_);
v___y_1960_ = v___y_1968_;
v___y_1961_ = v___x_1972_;
goto v___jp_1959_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkNodeToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1942_ = stack[0].m_obj;
lean_object* v_startPos_1943_ = stack[1].m_obj;
uint8_t v_includeWhitespace_1944_ = stack[2].m_num;
lean_object* v_c_1945_ = stack[3].m_obj;
lean_object* v_s_1946_ = stack[4].m_obj;
lean_object* v_res_1978_;
v_res_1978_ = l_Lean_Parser_mkNodeToken(v_n_1942_, v_startPos_1943_, v_includeWhitespace_1944_, v_c_1945_, v_s_1946_);
stack->m_obj
 = v_res_1978_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1979_, lean_object* v_startPos_1980_, lean_object* v_includeWhitespace_1981_, lean_object* v_c_1982_, lean_object* v_s_1983_){
_start:
{
uint8_t v_includeWhitespace_boxed_1984_; lean_object* v_res_1985_; 
v_includeWhitespace_boxed_1984_ = lean_unbox(v_includeWhitespace_1981_);
v_res_1985_ = l_Lean_Parser_mkNodeToken(v_n_1979_, v_startPos_1980_, v_includeWhitespace_boxed_1984_, v_c_1982_, v_s_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1990_, lean_object* v_c_1991_, lean_object* v_s_1992_){
_start:
{
lean_object* v_pos_1993_; lean_object* v_toInputContext_1994_; uint8_t v___x_1995_; 
v_pos_1993_ = lean_ctor_get(v_s_1992_, 2);
v_toInputContext_1994_ = lean_ctor_get(v_c_1991_, 0);
v___x_1995_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1994_, v_pos_1993_);
if (v___x_1995_ == 0)
{
lean_object* v_inputString_1996_; uint8_t v___x_1997_; lean_object* v___y_1999_; uint32_t v_curr_2014_; lean_object* v___x_2015_; lean_object* v_s_2016_; uint32_t v___x_2017_; uint8_t v___x_2018_; 
v_inputString_1996_ = lean_ctor_get(v_toInputContext_1994_, 0);
v___x_1997_ = 1;
v_curr_2014_ = lean_string_utf8_get_fast(v_inputString_1996_, v_pos_1993_);
v___x_2015_ = lean_string_utf8_next_fast(v_inputString_1996_, v_pos_1993_);
v_s_2016_ = l_Lean_Parser_ParserState_setPos(v_s_1992_, v___x_2015_);
v___x_2017_ = 92;
v___x_2018_ = lean_uint32_dec_eq(v_curr_2014_, v___x_2017_);
if (v___x_2018_ == 0)
{
v___y_1999_ = v_s_2016_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2019_; 
lean_inc_ref(v_c_1991_);
v___x_2019_ = l_Lean_Parser_quotedCharFn(v_c_1991_, v_s_2016_);
v___y_1999_ = v___x_2019_;
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v_pos_2000_; lean_object* v_errorMsg_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_pos_2000_ = lean_ctor_get(v___y_1999_, 2);
v_errorMsg_2001_ = lean_ctor_get(v___y_1999_, 4);
v___x_2002_ = lean_box(0);
v___x_2003_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v_c_1991_);
lean_dec(v_startPos_1990_);
return v___y_1999_;
}
else
{
if (v___x_1995_ == 0)
{
uint32_t v_curr_2004_; lean_object* v___x_2005_; lean_object* v_s_2006_; uint32_t v___x_2007_; uint8_t v___x_2008_; 
v_curr_2004_ = lean_string_utf8_get(v_inputString_1996_, v_pos_2000_);
v___x_2005_ = lean_string_utf8_next(v_inputString_1996_, v_pos_2000_);
v_s_2006_ = l_Lean_Parser_ParserState_setPos(v___y_1999_, v___x_2005_);
v___x_2007_ = 39;
v___x_2008_ = lean_uint32_dec_eq(v_curr_2004_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_dec_ref(v_c_1991_);
lean_dec(v_startPos_1990_);
v___x_2009_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_2010_ = lean_box(0);
v___x_2011_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2006_, v___x_2009_, v___x_2010_, v___x_1997_);
return v___x_2011_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_2013_ = l_Lean_Parser_mkNodeToken(v___x_2012_, v_startPos_1990_, v___x_1997_, v_c_1991_, v_s_2006_);
return v___x_2013_;
}
}
else
{
lean_dec_ref(v_c_1991_);
lean_dec(v_startPos_1990_);
return v___y_1999_;
}
}
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec_ref(v_c_1991_);
lean_dec(v_startPos_1990_);
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1992_, v___x_2020_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_2026_, lean_object* v_includeWhitespace_2027_, lean_object* v_c_2028_, lean_object* v_s_2029_){
_start:
{
uint8_t v_includeWhitespace_boxed_2030_; lean_object* v_res_2031_; 
v_includeWhitespace_boxed_2030_ = lean_unbox(v_includeWhitespace_2027_);
v_res_2031_ = l_Lean_Parser_strLitFnAux(v_startPos_2026_, v_includeWhitespace_boxed_2030_, v_c_2028_, v_s_2029_);
return v_res_2031_;
}
}
lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_2032_, uint8_t v_includeWhitespace_2033_, lean_object* v_c_2034_, lean_object* v_s_2035_){
_start:
{
lean_object* v_pos_2036_; lean_object* v_toInputContext_2037_; uint8_t v___x_2038_; 
v_pos_2036_ = lean_ctor_get(v_s_2035_, 2);
v_toInputContext_2037_ = lean_ctor_get(v_c_2034_, 0);
v___x_2038_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2037_, v_pos_2036_);
if (v___x_2038_ == 0)
{
lean_object* v_inputString_2039_; uint32_t v_curr_2040_; lean_object* v___x_2041_; lean_object* v_s_2042_; uint32_t v___x_2043_; uint8_t v___x_2044_; 
v_inputString_2039_ = lean_ctor_get(v_toInputContext_2037_, 0);
v_curr_2040_ = lean_string_utf8_get_fast(v_inputString_2039_, v_pos_2036_);
v___x_2041_ = lean_string_utf8_next_fast(v_inputString_2039_, v_pos_2036_);
v_s_2042_ = l_Lean_Parser_ParserState_setPos(v_s_2035_, v___x_2041_);
v___x_2043_ = 34;
v___x_2044_ = lean_uint32_dec_eq(v_curr_2040_, v___x_2043_);
if (v___x_2044_ == 0)
{
uint32_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = 92;
v___x_2046_ = lean_uint32_dec_eq(v_curr_2040_, v___x_2045_);
if (v___x_2046_ == 0)
{
v_s_2035_ = v_s_2042_;
goto _start;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_2049_ = lean_box(v_includeWhitespace_2033_);
v___x_2050_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_2050_, 0, v_startPos_2032_);
lean_closure_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_Parser_andthenFn(v___x_2048_, v___x_2050_, v_c_2034_, v_s_2042_);
return v___x_2051_;
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2053_ = l_Lean_Parser_mkNodeToken(v___x_2052_, v_startPos_2032_, v_includeWhitespace_2033_, v_c_2034_, v_s_2042_);
return v___x_2053_;
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref(v_c_2034_);
v___x_2054_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_2055_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2035_, v___x_2054_, v_startPos_2032_);
return v___x_2055_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_strLitFnAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2032_ = stack[0].m_obj;
uint8_t v_includeWhitespace_2033_ = stack[1].m_num;
lean_object* v_c_2034_ = stack[2].m_obj;
lean_object* v_s_2035_ = stack[3].m_obj;
lean_object* v_res_2056_;
v_res_2056_ = l_Lean_Parser_strLitFnAux(v_startPos_2032_, v_includeWhitespace_2033_, v_c_2034_, v_s_2035_);
stack->m_obj
 = v_res_2056_;
}
uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_2057_, lean_object* v_i_2058_){
_start:
{
lean_object* v_toInputContext_2059_; uint8_t v___x_2060_; 
v_toInputContext_2059_ = lean_ctor_get(v_c_2057_, 0);
v___x_2060_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2059_, v_i_2058_);
if (v___x_2060_ == 0)
{
lean_object* v_inputString_2061_; uint32_t v_curr_2062_; uint32_t v___x_2063_; uint8_t v___x_2064_; 
v_inputString_2061_ = lean_ctor_get(v_toInputContext_2059_, 0);
v_curr_2062_ = lean_string_utf8_get_fast(v_inputString_2061_, v_i_2058_);
v___x_2063_ = 35;
v___x_2064_ = lean_uint32_dec_eq(v_curr_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
uint32_t v___x_2065_; uint8_t v___x_2066_; 
lean_dec(v_i_2058_);
v___x_2065_ = 34;
v___x_2066_ = lean_uint32_dec_eq(v_curr_2062_, v___x_2065_);
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_string_utf8_next_fast(v_inputString_2061_, v_i_2058_);
lean_dec(v_i_2058_);
v_i_2058_ = v___x_2067_;
goto _start;
}
}
else
{
uint8_t v___x_2069_; 
lean_dec(v_i_2058_);
v___x_2069_ = 0;
return v___x_2069_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_isRawStrLitStart_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2057_ = stack[0].m_obj;
lean_object* v_i_2058_ = stack[1].m_obj;
uint8_t v_res_2070_;
v_res_2070_ = l_Lean_Parser_isRawStrLitStart(v_c_2057_, v_i_2058_);
stack->m_num = v_res_2070_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2071_, lean_object* v_i_2072_){
_start:
{
uint8_t v_res_2073_; lean_object* v_r_2074_; 
v_res_2073_ = l_Lean_Parser_isRawStrLitStart(v_c_2071_, v_i_2072_);
lean_dec_ref(v_c_2071_);
v_r_2074_ = lean_box(v_res_2073_);
return v_r_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2076_, lean_object* v_s_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2079_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2077_, v___x_2078_, v_startPos_2076_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2080_, lean_object* v_num_2081_, lean_object* v_closingNum_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_pos_2085_; lean_object* v_toInputContext_2086_; uint8_t v___x_2087_; 
v_pos_2085_ = lean_ctor_get(v_a_2084_, 2);
v_toInputContext_2086_ = lean_ctor_get(v_a_2083_, 0);
v___x_2087_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2086_, v_pos_2085_);
if (v___x_2087_ == 0)
{
lean_object* v_inputString_2088_; uint32_t v_curr_2089_; lean_object* v___x_2090_; lean_object* v_s_2091_; uint32_t v___x_2092_; uint8_t v___x_2093_; 
v_inputString_2088_ = lean_ctor_get(v_toInputContext_2086_, 0);
v_curr_2089_ = lean_string_utf8_get_fast(v_inputString_2088_, v_pos_2085_);
v___x_2090_ = lean_string_utf8_next_fast(v_inputString_2088_, v_pos_2085_);
v_s_2091_ = l_Lean_Parser_ParserState_setPos(v_a_2084_, v___x_2090_);
v___x_2092_ = 35;
v___x_2093_ = lean_uint32_dec_eq(v_curr_2089_, v___x_2092_);
if (v___x_2093_ == 0)
{
uint32_t v___x_2094_; uint8_t v___x_2095_; 
lean_dec(v_closingNum_2082_);
v___x_2094_ = 34;
v___x_2095_ = lean_uint32_dec_eq(v_curr_2089_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2080_, v_num_2081_, v_a_2083_, v_s_2091_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_unsigned_to_nat(0u);
v_closingNum_2082_ = v___x_2097_;
v_a_2084_ = v_s_2091_;
goto _start;
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_closingNum_2082_, v___x_2099_);
lean_dec(v_closingNum_2082_);
v___x_2101_ = lean_nat_dec_eq(v___x_2100_, v_num_2081_);
if (v___x_2101_ == 0)
{
v_closingNum_2082_ = v___x_2100_;
v_a_2084_ = v_s_2091_;
goto _start;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec(v___x_2100_);
v___x_2103_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2104_ = l_Lean_Parser_mkNodeToken(v___x_2103_, v_startPos_2080_, v___x_2101_, v_a_2083_, v_s_2091_);
return v___x_2104_;
}
}
}
else
{
lean_object* v___x_2105_; 
lean_dec_ref(v_a_2083_);
lean_dec(v_closingNum_2082_);
v___x_2105_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2080_, v_a_2084_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2106_, lean_object* v_num_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_pos_2110_; lean_object* v_toInputContext_2111_; uint8_t v___x_2112_; 
v_pos_2110_ = lean_ctor_get(v_a_2109_, 2);
v_toInputContext_2111_ = lean_ctor_get(v_a_2108_, 0);
v___x_2112_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2111_, v_pos_2110_);
if (v___x_2112_ == 0)
{
lean_object* v_inputString_2113_; uint32_t v_curr_2114_; lean_object* v___x_2115_; lean_object* v_s_2116_; uint32_t v___x_2117_; uint8_t v___x_2118_; 
v_inputString_2113_ = lean_ctor_get(v_toInputContext_2111_, 0);
v_curr_2114_ = lean_string_utf8_get_fast(v_inputString_2113_, v_pos_2110_);
v___x_2115_ = lean_string_utf8_next_fast(v_inputString_2113_, v_pos_2110_);
v_s_2116_ = l_Lean_Parser_ParserState_setPos(v_a_2109_, v___x_2115_);
v___x_2117_ = 34;
v___x_2118_ = lean_uint32_dec_eq(v_curr_2114_, v___x_2117_);
if (v___x_2118_ == 0)
{
v_a_2109_ = v_s_2116_;
goto _start;
}
else
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_nat_dec_eq(v_num_2107_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2106_, v_num_2107_, v___x_2120_, v_a_2108_, v_s_2116_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2124_ = l_Lean_Parser_mkNodeToken(v___x_2123_, v_startPos_2106_, v___x_2121_, v_a_2108_, v_s_2116_);
return v___x_2124_;
}
}
}
else
{
lean_object* v___x_2125_; 
lean_dec_ref(v_a_2108_);
v___x_2125_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2106_, v_a_2109_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2126_, lean_object* v_num_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2126_, v_num_2127_, v_a_2128_, v_a_2129_);
lean_dec(v_num_2127_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2131_, lean_object* v_num_2132_, lean_object* v_closingNum_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2131_, v_num_2132_, v_closingNum_2133_, v_a_2134_, v_a_2135_);
lean_dec(v_num_2132_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2137_, lean_object* v_num_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_pos_2141_; lean_object* v_toInputContext_2142_; uint8_t v___x_2143_; 
v_pos_2141_ = lean_ctor_get(v_a_2140_, 2);
v_toInputContext_2142_ = lean_ctor_get(v_a_2139_, 0);
v___x_2143_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2142_, v_pos_2141_);
if (v___x_2143_ == 0)
{
lean_object* v_inputString_2144_; uint32_t v_curr_2145_; lean_object* v___x_2146_; lean_object* v_s_2147_; uint32_t v___x_2148_; uint8_t v___x_2149_; 
v_inputString_2144_ = lean_ctor_get(v_toInputContext_2142_, 0);
v_curr_2145_ = lean_string_utf8_get_fast(v_inputString_2144_, v_pos_2141_);
v___x_2146_ = lean_string_utf8_next_fast(v_inputString_2144_, v_pos_2141_);
v_s_2147_ = l_Lean_Parser_ParserState_setPos(v_a_2140_, v___x_2146_);
v___x_2148_ = 35;
v___x_2149_ = lean_uint32_dec_eq(v_curr_2145_, v___x_2148_);
if (v___x_2149_ == 0)
{
uint32_t v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = 34;
v___x_2151_ = lean_uint32_dec_eq(v_curr_2145_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_dec_ref(v_a_2139_);
lean_dec(v_num_2138_);
v___x_2152_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2137_, v_s_2147_);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2137_, v_num_2138_, v_a_2139_, v_s_2147_);
lean_dec(v_num_2138_);
return v___x_2153_;
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(1u);
v___x_2155_ = lean_nat_add(v_num_2138_, v___x_2154_);
lean_dec(v_num_2138_);
v_num_2138_ = v___x_2155_;
v_a_2140_ = v_s_2147_;
goto _start;
}
}
else
{
lean_object* v___x_2157_; 
lean_dec_ref(v_a_2139_);
lean_dec(v_num_2138_);
v___x_2157_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2137_, v_a_2140_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2158_, v___x_2161_, v_a_2159_, v_a_2160_);
return v___x_2162_;
}
}
lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2164_, lean_object* v_expecting_2165_, uint8_t v_needDigit_2166_, lean_object* v_c_2167_, lean_object* v_s_2168_){
_start:
{
lean_object* v_pos_2169_; lean_object* v_toInputContext_2170_; uint8_t v___x_2171_; 
v_pos_2169_ = lean_ctor_get(v_s_2168_, 2);
v_toInputContext_2170_ = lean_ctor_get(v_c_2167_, 0);
v___x_2171_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2170_, v_pos_2169_);
if (v___x_2171_ == 0)
{
lean_object* v_inputString_2172_; uint8_t v___x_2173_; uint32_t v_curr_2174_; uint32_t v___x_2175_; uint8_t v___x_2176_; 
v_inputString_2172_ = lean_ctor_get(v_toInputContext_2170_, 0);
v___x_2173_ = 1;
v_curr_2174_ = lean_string_utf8_get_fast(v_inputString_2172_, v_pos_2169_);
v___x_2175_ = 95;
v___x_2176_ = lean_uint32_dec_eq(v_curr_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2177_ = lean_box_uint32(v_curr_2174_);
lean_inc_ref(v_isDigit_2164_);
v___x_2178_ = lean_apply_1(v_isDigit_2164_, v___x_2177_);
v___x_2179_ = lean_unbox(v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec_ref(v_isDigit_2164_);
if (v_needDigit_2166_ == 0)
{
lean_dec_ref(v_expecting_2165_);
return v_s_2168_;
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_expecting_2165_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2168_, v___x_2180_, v___x_2182_, v___x_2173_);
return v___x_2183_;
}
}
else
{
lean_object* v___x_2184_; 
lean_inc(v_pos_2169_);
v___x_2184_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2168_, v_c_2167_, v_pos_2169_);
lean_dec(v_pos_2169_);
v_needDigit_2166_ = v___x_2176_;
v_s_2168_ = v___x_2184_;
goto _start;
}
}
else
{
lean_object* v___x_2186_; 
lean_inc(v_pos_2169_);
v___x_2186_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2168_, v_c_2167_, v_pos_2169_);
lean_dec(v_pos_2169_);
v_needDigit_2166_ = v___x_2173_;
v_s_2168_ = v___x_2186_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2164_);
if (v_needDigit_2166_ == 0)
{
lean_dec_ref(v_expecting_2165_);
return v_s_2168_;
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_expecting_2165_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2168_, v___x_2189_);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_takeDigitsFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_isDigit_2164_ = stack[0].m_obj;
lean_object* v_expecting_2165_ = stack[1].m_obj;
uint8_t v_needDigit_2166_ = stack[2].m_num;
lean_object* v_c_2167_ = stack[3].m_obj;
lean_object* v_s_2168_ = stack[4].m_obj;
lean_object* v_res_2191_;
v_res_2191_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2164_, v_expecting_2165_, v_needDigit_2166_, v_c_2167_, v_s_2168_);
stack->m_obj
 = v_res_2191_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2192_, lean_object* v_expecting_2193_, lean_object* v_needDigit_2194_, lean_object* v_c_2195_, lean_object* v_s_2196_){
_start:
{
uint8_t v_needDigit_boxed_2197_; lean_object* v_res_2198_; 
v_needDigit_boxed_2197_ = lean_unbox(v_needDigit_2194_);
v_res_2198_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2192_, v_expecting_2193_, v_needDigit_boxed_2197_, v_c_2195_, v_s_2196_);
lean_dec_ref(v_c_2195_);
return v_res_2198_;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2199_){
_start:
{
uint32_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = 48;
v___x_2201_ = lean_uint32_dec_le(v___x_2200_, v_c_2199_);
if (v___x_2201_ == 0)
{
return v___x_2201_;
}
else
{
uint32_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = 57;
v___x_2203_ = lean_uint32_dec_le(v_c_2199_, v___x_2202_);
return v___x_2203_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_2199_ = stack[0].m_num;
uint8_t v_res_2204_;
v_res_2204_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_2199_);
stack->m_num = v_res_2204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2205_){
_start:
{
uint32_t v_c_boxed_2206_; uint8_t v_res_2207_; lean_object* v_r_2208_; 
v_c_boxed_2206_ = lean_unbox_uint32(v_c_2205_);
lean_dec(v_c_2205_);
v_res_2207_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2206_);
v_r_2208_ = lean_box(v_res_2207_);
return v_r_2208_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2213_, lean_object* v_c_2214_, lean_object* v_s_2215_, uint8_t v_hasBareDot_2216_){
_start:
{
lean_object* v_toInputContext_2217_; lean_object* v_pos_2218_; uint8_t v___x_2219_; 
v_toInputContext_2217_ = lean_ctor_get(v_c_2214_, 0);
v_pos_2218_ = lean_ctor_get(v_s_2215_, 2);
v___x_2219_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2217_, v_pos_2218_);
if (v___x_2219_ == 0)
{
lean_object* v_inputString_2220_; lean_object* v___f_2221_; uint8_t v___x_2222_; lean_object* v___y_2228_; lean_object* v___y_2238_; lean_object* v___y_2239_; uint32_t v_curr_2253_; uint32_t v___x_2265_; uint8_t v___x_2266_; 
v_inputString_2220_ = lean_ctor_get(v_toInputContext_2217_, 0);
v___f_2221_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2222_ = 1;
v_curr_2253_ = lean_string_utf8_get_fast(v_inputString_2220_, v_pos_2218_);
v___x_2265_ = 101;
v___x_2266_ = lean_uint32_dec_eq(v_curr_2253_, v___x_2265_);
if (v___x_2266_ == 0)
{
uint32_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = 69;
v___x_2268_ = lean_uint32_dec_eq(v_curr_2253_, v___x_2267_);
if (v___x_2268_ == 0)
{
if (v_hasBareDot_2216_ == 0)
{
lean_dec(v_startPos_2213_);
return v_s_2215_;
}
else
{
uint32_t v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = 65;
v___x_2270_ = lean_uint32_dec_le(v___x_2269_, v_curr_2253_);
if (v___x_2270_ == 0)
{
goto v___jp_2260_;
}
else
{
uint32_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = 90;
v___x_2272_ = lean_uint32_dec_le(v_curr_2253_, v___x_2271_);
if (v___x_2272_ == 0)
{
goto v___jp_2260_;
}
else
{
goto v___jp_2248_;
}
}
}
}
else
{
lean_dec(v_startPos_2213_);
goto v___jp_2241_;
}
}
else
{
lean_dec(v_startPos_2213_);
goto v___jp_2241_;
}
v___jp_2223_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2215_, v___x_2224_, v___x_2225_, v___x_2222_);
return v___x_2226_;
}
v___jp_2227_:
{
uint32_t v_curr_2229_; uint32_t v___x_2230_; uint8_t v___x_2231_; 
v_curr_2229_ = lean_string_utf8_get(v_inputString_2220_, v___y_2228_);
v___x_2230_ = 48;
v___x_2231_ = lean_uint32_dec_le(v___x_2230_, v_curr_2229_);
if (v___x_2231_ == 0)
{
lean_dec(v___y_2228_);
goto v___jp_2223_;
}
else
{
uint32_t v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = 57;
v___x_2233_ = lean_uint32_dec_le(v_curr_2229_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec(v___y_2228_);
goto v___jp_2223_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2235_ = l_Lean_Parser_ParserState_setPos(v_s_2215_, v___y_2228_);
v___x_2236_ = l_Lean_Parser_takeDigitsFn(v___f_2221_, v___x_2234_, v___x_2219_, v_c_2214_, v___x_2235_);
return v___x_2236_;
}
}
}
v___jp_2237_:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_string_utf8_next(v___y_2239_, v___y_2238_);
lean_dec(v___y_2238_);
v___y_2228_ = v___x_2240_;
goto v___jp_2227_;
}
v___jp_2241_:
{
lean_object* v_i_2242_; uint32_t v___x_2243_; uint32_t v___x_2244_; uint8_t v___x_2245_; 
v_i_2242_ = lean_string_utf8_next(v_inputString_2220_, v_pos_2218_);
v___x_2243_ = lean_string_utf8_get(v_inputString_2220_, v_i_2242_);
v___x_2244_ = 45;
v___x_2245_ = lean_uint32_dec_eq(v___x_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
uint32_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2246_ = 43;
v___x_2247_ = lean_uint32_dec_eq(v___x_2243_, v___x_2246_);
if (v___x_2247_ == 0)
{
v___y_2228_ = v_i_2242_;
goto v___jp_2227_;
}
else
{
v___y_2238_ = v_i_2242_;
v___y_2239_ = v_inputString_2220_;
goto v___jp_2237_;
}
}
else
{
v___y_2238_ = v_i_2242_;
v___y_2239_ = v_inputString_2220_;
goto v___jp_2237_;
}
}
v___jp_2248_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2249_ = l_Lean_Parser_ParserState_setPos(v_s_2215_, v_startPos_2213_);
v___x_2250_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2251_ = lean_box(0);
v___x_2252_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2249_, v___x_2250_, v___x_2251_, v___x_2222_);
return v___x_2252_;
}
v___jp_2254_:
{
uint32_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = 95;
v___x_2256_ = lean_uint32_dec_eq(v_curr_2253_, v___x_2255_);
if (v___x_2256_ == 0)
{
uint8_t v___x_2257_; 
v___x_2257_ = l_Lean_isLetterLike(v_curr_2253_);
if (v___x_2257_ == 0)
{
uint32_t v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = l_Lean_idBeginEscape;
v___x_2259_ = lean_uint32_dec_eq(v_curr_2253_, v___x_2258_);
if (v___x_2259_ == 0)
{
lean_dec(v_startPos_2213_);
return v_s_2215_;
}
else
{
goto v___jp_2248_;
}
}
else
{
goto v___jp_2248_;
}
}
else
{
goto v___jp_2248_;
}
}
v___jp_2260_:
{
uint32_t v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = 97;
v___x_2262_ = lean_uint32_dec_le(v___x_2261_, v_curr_2253_);
if (v___x_2262_ == 0)
{
goto v___jp_2254_;
}
else
{
uint32_t v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = 122;
v___x_2264_ = lean_uint32_dec_le(v_curr_2253_, v___x_2263_);
if (v___x_2264_ == 0)
{
goto v___jp_2254_;
}
else
{
goto v___jp_2248_;
}
}
}
}
else
{
lean_dec(v_startPos_2213_);
return v_s_2215_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2213_ = stack[0].m_obj;
lean_object* v_c_2214_ = stack[1].m_obj;
lean_object* v_s_2215_ = stack[2].m_obj;
uint8_t v_hasBareDot_2216_ = stack[3].m_num;
lean_object* v_res_2273_;
v_res_2273_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2213_, v_c_2214_, v_s_2215_, v_hasBareDot_2216_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2274_, lean_object* v_c_2275_, lean_object* v_s_2276_, lean_object* v_hasBareDot_2277_){
_start:
{
uint8_t v_hasBareDot_boxed_2278_; lean_object* v_res_2279_; 
v_hasBareDot_boxed_2278_ = lean_unbox(v_hasBareDot_2277_);
v_res_2279_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2274_, v_c_2275_, v_s_2276_, v_hasBareDot_boxed_2278_);
lean_dec_ref(v_c_2275_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2280_, lean_object* v_s_2281_){
_start:
{
lean_object* v_toInputContext_2282_; lean_object* v_pos_2283_; lean_object* v_inputString_2284_; uint32_t v_curr_2285_; uint32_t v___x_2286_; uint8_t v___x_2287_; 
v_toInputContext_2282_ = lean_ctor_get(v_c_2280_, 0);
v_pos_2283_ = lean_ctor_get(v_s_2281_, 2);
v_inputString_2284_ = lean_ctor_get(v_toInputContext_2282_, 0);
v_curr_2285_ = lean_string_utf8_get(v_inputString_2284_, v_pos_2283_);
v___x_2286_ = 46;
v___x_2287_ = lean_uint32_dec_eq(v_curr_2285_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_box(v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_s_2281_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
return v___x_2289_;
}
else
{
lean_object* v_i_2290_; uint32_t v_curr_2295_; uint32_t v___x_2296_; uint8_t v___x_2297_; 
v_i_2290_ = lean_string_utf8_next(v_inputString_2284_, v_pos_2283_);
v_curr_2295_ = lean_string_utf8_get(v_inputString_2284_, v_i_2290_);
v___x_2296_ = 48;
v___x_2297_ = lean_uint32_dec_le(v___x_2296_, v_curr_2295_);
if (v___x_2297_ == 0)
{
goto v___jp_2291_;
}
else
{
uint32_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = 57;
v___x_2299_ = lean_uint32_dec_le(v_curr_2295_, v___x_2298_);
if (v___x_2299_ == 0)
{
goto v___jp_2291_;
}
else
{
lean_object* v___f_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___f_2300_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2301_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2302_ = 0;
v___x_2303_ = l_Lean_Parser_ParserState_setPos(v_s_2281_, v_i_2290_);
v___x_2304_ = l_Lean_Parser_takeDigitsFn(v___f_2300_, v___x_2301_, v___x_2302_, v_c_2280_, v___x_2303_);
v___x_2305_ = lean_box(v___x_2302_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
return v___x_2306_;
}
}
v___jp_2291_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = l_Lean_Parser_ParserState_setPos(v_s_2281_, v_i_2290_);
v___x_2293_ = lean_box(v___x_2287_);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
return v___x_2294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2307_, lean_object* v_s_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2307_, v_s_2308_);
lean_dec_ref(v_c_2307_);
return v_res_2309_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2313_, uint8_t v_includeWhitespace_2314_, lean_object* v_c_2315_, lean_object* v_s_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v_fst_2318_; lean_object* v_snd_2319_; uint8_t v___x_2320_; lean_object* v_s_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2317_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2315_, v_s_2316_);
v_fst_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_fst_2318_);
v_snd_2319_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_snd_2319_);
lean_dec_ref(v___x_2317_);
v___x_2320_ = lean_unbox(v_snd_2319_);
lean_dec(v_snd_2319_);
lean_inc(v_startPos_2313_);
v_s_2321_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2313_, v_c_2315_, v_fst_2318_, v___x_2320_);
v___x_2322_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2323_ = l_Lean_Parser_mkNodeToken(v___x_2322_, v_startPos_2313_, v_includeWhitespace_2314_, v_c_2315_, v_s_2321_);
return v___x_2323_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2313_ = stack[0].m_obj;
uint8_t v_includeWhitespace_2314_ = stack[1].m_num;
lean_object* v_c_2315_ = stack[2].m_obj;
lean_object* v_s_2316_ = stack[3].m_obj;
lean_object* v_res_2324_;
v_res_2324_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2313_, v_includeWhitespace_2314_, v_c_2315_, v_s_2316_);
stack->m_obj
 = v_res_2324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2325_, lean_object* v_includeWhitespace_2326_, lean_object* v_c_2327_, lean_object* v_s_2328_){
_start:
{
uint8_t v_includeWhitespace_boxed_2329_; lean_object* v_res_2330_; 
v_includeWhitespace_boxed_2329_ = lean_unbox(v_includeWhitespace_2326_);
v_res_2330_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2325_, v_includeWhitespace_boxed_2329_, v_c_2327_, v_s_2328_);
return v_res_2330_;
}
}
lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2334_, uint8_t v_includeWhitespace_2335_, lean_object* v_c_2336_, lean_object* v_s_2337_){
_start:
{
lean_object* v___f_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v_s_2341_; lean_object* v_pos_2342_; lean_object* v_toInputContext_2343_; uint8_t v___x_2344_; 
v___f_2338_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2339_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2340_ = 0;
v_s_2341_ = l_Lean_Parser_takeDigitsFn(v___f_2338_, v___x_2339_, v___x_2340_, v_c_2336_, v_s_2337_);
v_pos_2342_ = lean_ctor_get(v_s_2341_, 2);
v_toInputContext_2343_ = lean_ctor_get(v_c_2336_, 0);
v___x_2344_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2343_, v_pos_2342_);
if (v___x_2344_ == 0)
{
lean_object* v_inputString_2345_; uint32_t v_curr_2346_; lean_object* v_j_2359_; uint8_t v___x_2367_; 
v_inputString_2345_ = lean_ctor_get(v_toInputContext_2343_, 0);
v_curr_2346_ = lean_string_utf8_get_fast(v_inputString_2345_, v_pos_2342_);
v_j_2359_ = lean_string_utf8_next(v_inputString_2345_, v_pos_2342_);
v___x_2367_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2343_, v_j_2359_);
if (v___x_2367_ == 0)
{
goto v___jp_2360_;
}
else
{
if (v___x_2344_ == 0)
{
lean_dec(v_j_2359_);
goto v___jp_2347_;
}
else
{
goto v___jp_2360_;
}
}
v___jp_2347_:
{
uint32_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = 46;
v___x_2349_ = lean_uint32_dec_eq(v_curr_2346_, v___x_2348_);
if (v___x_2349_ == 0)
{
uint32_t v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = 101;
v___x_2351_ = lean_uint32_dec_eq(v_curr_2346_, v___x_2350_);
if (v___x_2351_ == 0)
{
uint32_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = 69;
v___x_2353_ = lean_uint32_dec_eq(v_curr_2346_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2355_ = l_Lean_Parser_mkNodeToken(v___x_2354_, v_startPos_2334_, v_includeWhitespace_2335_, v_c_2336_, v_s_2341_);
return v___x_2355_;
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2334_, v_includeWhitespace_2335_, v_c_2336_, v_s_2341_);
return v___x_2356_;
}
}
else
{
lean_object* v___x_2357_; 
v___x_2357_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2334_, v_includeWhitespace_2335_, v_c_2336_, v_s_2341_);
return v___x_2357_;
}
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2334_, v_includeWhitespace_2335_, v_c_2336_, v_s_2341_);
return v___x_2358_;
}
}
v___jp_2360_:
{
uint32_t v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = 46;
v___x_2362_ = lean_uint32_dec_eq(v_curr_2346_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_dec(v_j_2359_);
goto v___jp_2347_;
}
else
{
uint32_t v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_string_utf8_get_fast(v_inputString_2345_, v_j_2359_);
lean_dec(v_j_2359_);
v___x_2364_ = lean_uint32_dec_eq(v___x_2363_, v___x_2361_);
if (v___x_2364_ == 0)
{
goto v___jp_2347_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2366_ = l_Lean_Parser_mkNodeToken(v___x_2365_, v_startPos_2334_, v_includeWhitespace_2335_, v_c_2336_, v_s_2341_);
return v___x_2366_;
}
}
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2369_ = l_Lean_Parser_mkNodeToken(v___x_2368_, v_startPos_2334_, v___x_2344_, v_c_2336_, v_s_2341_);
return v___x_2369_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_decimalNumberFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2334_ = stack[0].m_obj;
uint8_t v_includeWhitespace_2335_ = stack[1].m_num;
lean_object* v_c_2336_ = stack[2].m_obj;
lean_object* v_s_2337_ = stack[3].m_obj;
lean_object* v_res_2370_;
v_res_2370_ = l_Lean_Parser_decimalNumberFn(v_startPos_2334_, v_includeWhitespace_2335_, v_c_2336_, v_s_2337_);
stack->m_obj
 = v_res_2370_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2371_, lean_object* v_includeWhitespace_2372_, lean_object* v_c_2373_, lean_object* v_s_2374_){
_start:
{
uint8_t v_includeWhitespace_boxed_2375_; lean_object* v_res_2376_; 
v_includeWhitespace_boxed_2375_ = lean_unbox(v_includeWhitespace_2372_);
v_res_2376_ = l_Lean_Parser_decimalNumberFn(v_startPos_2371_, v_includeWhitespace_boxed_2375_, v_c_2373_, v_s_2374_);
return v_res_2376_;
}
}
uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2377_){
_start:
{
uint32_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = 48;
v___x_2379_ = lean_uint32_dec_eq(v_c_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
uint32_t v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = 49;
v___x_2381_ = lean_uint32_dec_eq(v_c_2377_, v___x_2380_);
return v___x_2381_;
}
else
{
return v___x_2379_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_binNumberFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_2377_ = stack[0].m_num;
uint8_t v_res_2382_;
v_res_2382_ = l_Lean_Parser_binNumberFn___lam__0(v_c_2377_);
stack->m_num = v_res_2382_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2383_){
_start:
{
uint32_t v_c_boxed_2384_; uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_c_boxed_2384_ = lean_unbox_uint32(v_c_2383_);
lean_dec(v_c_2383_);
v_res_2385_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2384_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2389_, uint8_t v_includeWhitespace_2390_, lean_object* v_c_2391_, lean_object* v_s_2392_){
_start:
{
lean_object* v___f_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v_s_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___f_2393_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2394_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2395_ = 1;
v_s_2396_ = l_Lean_Parser_takeDigitsFn(v___f_2393_, v___x_2394_, v___x_2395_, v_c_2391_, v_s_2392_);
v___x_2397_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2398_ = l_Lean_Parser_mkNodeToken(v___x_2397_, v_startPos_2389_, v_includeWhitespace_2390_, v_c_2391_, v_s_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT void l_Lean_Parser_binNumberFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2389_ = stack[0].m_obj;
uint8_t v_includeWhitespace_2390_ = stack[1].m_num;
lean_object* v_c_2391_ = stack[2].m_obj;
lean_object* v_s_2392_ = stack[3].m_obj;
lean_object* v_res_2399_;
v_res_2399_ = l_Lean_Parser_binNumberFn(v_startPos_2389_, v_includeWhitespace_2390_, v_c_2391_, v_s_2392_);
stack->m_obj
 = v_res_2399_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2400_, lean_object* v_includeWhitespace_2401_, lean_object* v_c_2402_, lean_object* v_s_2403_){
_start:
{
uint8_t v_includeWhitespace_boxed_2404_; lean_object* v_res_2405_; 
v_includeWhitespace_boxed_2404_ = lean_unbox(v_includeWhitespace_2401_);
v_res_2405_ = l_Lean_Parser_binNumberFn(v_startPos_2400_, v_includeWhitespace_boxed_2404_, v_c_2402_, v_s_2403_);
return v_res_2405_;
}
}
uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2406_){
_start:
{
uint32_t v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = 48;
v___x_2408_ = lean_uint32_dec_le(v___x_2407_, v_c_2406_);
if (v___x_2408_ == 0)
{
return v___x_2408_;
}
else
{
uint32_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = 55;
v___x_2410_ = lean_uint32_dec_le(v_c_2406_, v___x_2409_);
return v___x_2410_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_octalNumberFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_2406_ = stack[0].m_num;
uint8_t v_res_2411_;
v_res_2411_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_2406_);
stack->m_num = v_res_2411_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2412_){
_start:
{
uint32_t v_c_boxed_2413_; uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_c_boxed_2413_ = lean_unbox_uint32(v_c_2412_);
lean_dec(v_c_2412_);
v_res_2414_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2413_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2418_, uint8_t v_includeWhitespace_2419_, lean_object* v_c_2420_, lean_object* v_s_2421_){
_start:
{
lean_object* v___f_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v_s_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___f_2422_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2423_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2424_ = 1;
v_s_2425_ = l_Lean_Parser_takeDigitsFn(v___f_2422_, v___x_2423_, v___x_2424_, v_c_2420_, v_s_2421_);
v___x_2426_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2427_ = l_Lean_Parser_mkNodeToken(v___x_2426_, v_startPos_2418_, v_includeWhitespace_2419_, v_c_2420_, v_s_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT void l_Lean_Parser_octalNumberFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2418_ = stack[0].m_obj;
uint8_t v_includeWhitespace_2419_ = stack[1].m_num;
lean_object* v_c_2420_ = stack[2].m_obj;
lean_object* v_s_2421_ = stack[3].m_obj;
lean_object* v_res_2428_;
v_res_2428_ = l_Lean_Parser_octalNumberFn(v_startPos_2418_, v_includeWhitespace_2419_, v_c_2420_, v_s_2421_);
stack->m_obj
 = v_res_2428_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2429_, lean_object* v_includeWhitespace_2430_, lean_object* v_c_2431_, lean_object* v_s_2432_){
_start:
{
uint8_t v_includeWhitespace_boxed_2433_; lean_object* v_res_2434_; 
v_includeWhitespace_boxed_2433_ = lean_unbox(v_includeWhitespace_2430_);
v_res_2434_ = l_Lean_Parser_octalNumberFn(v_startPos_2429_, v_includeWhitespace_boxed_2433_, v_c_2431_, v_s_2432_);
return v_res_2434_;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2435_){
_start:
{
uint32_t v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = 48;
v___x_2447_ = lean_uint32_dec_le(v___x_2446_, v_c_2435_);
if (v___x_2447_ == 0)
{
goto v___jp_2441_;
}
else
{
uint32_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = 57;
v___x_2449_ = lean_uint32_dec_le(v_c_2435_, v___x_2448_);
if (v___x_2449_ == 0)
{
goto v___jp_2441_;
}
else
{
return v___x_2449_;
}
}
v___jp_2436_:
{
uint32_t v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = 65;
v___x_2438_ = lean_uint32_dec_le(v___x_2437_, v_c_2435_);
if (v___x_2438_ == 0)
{
return v___x_2438_;
}
else
{
uint32_t v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = 70;
v___x_2440_ = lean_uint32_dec_le(v_c_2435_, v___x_2439_);
return v___x_2440_;
}
}
v___jp_2441_:
{
uint32_t v___x_2442_; uint8_t v___x_2443_; 
v___x_2442_ = 97;
v___x_2443_ = lean_uint32_dec_le(v___x_2442_, v_c_2435_);
if (v___x_2443_ == 0)
{
goto v___jp_2436_;
}
else
{
uint32_t v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = 102;
v___x_2445_ = lean_uint32_dec_le(v_c_2435_, v___x_2444_);
if (v___x_2445_ == 0)
{
goto v___jp_2436_;
}
else
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_2435_ = stack[0].m_num;
uint8_t v_res_2450_;
v_res_2450_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_2435_);
stack->m_num = v_res_2450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2451_){
_start:
{
uint32_t v_c_boxed_2452_; uint8_t v_res_2453_; lean_object* v_r_2454_; 
v_c_boxed_2452_ = lean_unbox_uint32(v_c_2451_);
lean_dec(v_c_2451_);
v_res_2453_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2452_);
v_r_2454_ = lean_box(v_res_2453_);
return v_r_2454_;
}
}
uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2455_){
_start:
{
uint32_t v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = 48;
v___x_2467_ = lean_uint32_dec_le(v___x_2466_, v___y_2455_);
if (v___x_2467_ == 0)
{
goto v___jp_2461_;
}
else
{
uint32_t v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = 57;
v___x_2469_ = lean_uint32_dec_le(v___y_2455_, v___x_2468_);
if (v___x_2469_ == 0)
{
goto v___jp_2461_;
}
else
{
return v___x_2469_;
}
}
v___jp_2456_:
{
uint32_t v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = 65;
v___x_2458_ = lean_uint32_dec_le(v___x_2457_, v___y_2455_);
if (v___x_2458_ == 0)
{
return v___x_2458_;
}
else
{
uint32_t v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = 70;
v___x_2460_ = lean_uint32_dec_le(v___y_2455_, v___x_2459_);
return v___x_2460_;
}
}
v___jp_2461_:
{
uint32_t v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = 97;
v___x_2463_ = lean_uint32_dec_le(v___x_2462_, v___y_2455_);
if (v___x_2463_ == 0)
{
goto v___jp_2456_;
}
else
{
uint32_t v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = 102;
v___x_2465_ = lean_uint32_dec_le(v___y_2455_, v___x_2464_);
if (v___x_2465_ == 0)
{
goto v___jp_2456_;
}
else
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_hexNumberFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_2455_ = stack[0].m_num;
uint8_t v_res_2470_;
v_res_2470_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_2455_);
stack->m_num = v_res_2470_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2471_){
_start:
{
uint32_t v___y_110__boxed_2472_; uint8_t v_res_2473_; lean_object* v_r_2474_; 
v___y_110__boxed_2472_ = lean_unbox_uint32(v___y_2471_);
lean_dec(v___y_2471_);
v_res_2473_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_110__boxed_2472_);
v_r_2474_ = lean_box(v_res_2473_);
return v_r_2474_;
}
}
lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2477_, uint8_t v_includeWhitespace_2478_, lean_object* v_kind_2479_, lean_object* v_c_2480_, lean_object* v_s_2481_){
_start:
{
lean_object* v___f_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v_s_2485_; lean_object* v___x_2486_; 
v___f_2482_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2483_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2484_ = 1;
v_s_2485_ = l_Lean_Parser_takeDigitsFn(v___f_2482_, v___x_2483_, v___x_2484_, v_c_2480_, v_s_2481_);
v___x_2486_ = l_Lean_Parser_mkNodeToken(v_kind_2479_, v_startPos_2477_, v_includeWhitespace_2478_, v_c_2480_, v_s_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT void l_Lean_Parser_hexNumberFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2477_ = stack[0].m_obj;
uint8_t v_includeWhitespace_2478_ = stack[1].m_num;
lean_object* v_kind_2479_ = stack[2].m_obj;
lean_object* v_c_2480_ = stack[3].m_obj;
lean_object* v_s_2481_ = stack[4].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l_Lean_Parser_hexNumberFn(v_startPos_2477_, v_includeWhitespace_2478_, v_kind_2479_, v_c_2480_, v_s_2481_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2488_, lean_object* v_includeWhitespace_2489_, lean_object* v_kind_2490_, lean_object* v_c_2491_, lean_object* v_s_2492_){
_start:
{
uint8_t v_includeWhitespace_boxed_2493_; lean_object* v_res_2494_; 
v_includeWhitespace_boxed_2493_ = lean_unbox(v_includeWhitespace_2489_);
v_res_2494_ = l_Lean_Parser_hexNumberFn(v_startPos_2488_, v_includeWhitespace_boxed_2493_, v_kind_2490_, v_c_2491_, v_s_2492_);
return v_res_2494_;
}
}
lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2496_, lean_object* v_c_2497_, lean_object* v_s_2498_){
_start:
{
lean_object* v_pos_2502_; lean_object* v_toInputContext_2503_; uint8_t v___x_2504_; 
v_pos_2502_ = lean_ctor_get(v_s_2498_, 2);
v_toInputContext_2503_ = lean_ctor_get(v_c_2497_, 0);
v___x_2504_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2503_, v_pos_2502_);
if (v___x_2504_ == 0)
{
lean_object* v_inputString_2505_; uint32_t v_curr_2506_; uint32_t v___x_2507_; uint8_t v___x_2508_; 
v_inputString_2505_ = lean_ctor_get(v_toInputContext_2503_, 0);
v_curr_2506_ = lean_string_utf8_get_fast(v_inputString_2505_, v_pos_2502_);
v___x_2507_ = 48;
v___x_2508_ = lean_uint32_dec_eq(v_curr_2506_, v___x_2507_);
if (v___x_2508_ == 0)
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_uint32_dec_le(v___x_2507_, v_curr_2506_);
if (v___x_2509_ == 0)
{
lean_dec_ref(v_c_2497_);
goto v___jp_2499_;
}
else
{
uint32_t v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = 57;
v___x_2511_ = lean_uint32_dec_le(v_curr_2506_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_dec_ref(v_c_2497_);
goto v___jp_2499_;
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_inc(v_pos_2502_);
v___x_2512_ = l_Lean_Parser_ParserState_next(v_s_2498_, v_c_2497_, v_pos_2502_);
v___x_2513_ = l_Lean_Parser_decimalNumberFn(v_pos_2502_, v_includeWhitespace_2496_, v_c_2497_, v___x_2512_);
return v___x_2513_;
}
}
}
else
{
lean_object* v_i_2514_; uint32_t v_curr_2525_; uint32_t v___x_2526_; uint8_t v___x_2527_; 
lean_inc(v_pos_2502_);
v_i_2514_ = lean_string_utf8_next_fast(v_inputString_2505_, v_pos_2502_);
v_curr_2525_ = lean_string_utf8_get(v_inputString_2505_, v_i_2514_);
v___x_2526_ = 98;
v___x_2527_ = lean_uint32_dec_eq(v_curr_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
uint32_t v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = 66;
v___x_2529_ = lean_uint32_dec_eq(v_curr_2525_, v___x_2528_);
if (v___x_2529_ == 0)
{
uint32_t v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = 111;
v___x_2531_ = lean_uint32_dec_eq(v_curr_2525_, v___x_2530_);
if (v___x_2531_ == 0)
{
uint32_t v___x_2532_; uint8_t v___x_2533_; 
v___x_2532_ = 79;
v___x_2533_ = lean_uint32_dec_eq(v_curr_2525_, v___x_2532_);
if (v___x_2533_ == 0)
{
uint32_t v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = 120;
v___x_2535_ = lean_uint32_dec_eq(v_curr_2525_, v___x_2534_);
if (v___x_2535_ == 0)
{
uint32_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = 88;
v___x_2537_ = lean_uint32_dec_eq(v_curr_2525_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = l_Lean_Parser_ParserState_setPos(v_s_2498_, v_i_2514_);
v___x_2539_ = l_Lean_Parser_decimalNumberFn(v_pos_2502_, v_includeWhitespace_2496_, v_c_2497_, v___x_2538_);
return v___x_2539_;
}
else
{
goto v___jp_2515_;
}
}
else
{
goto v___jp_2515_;
}
}
else
{
goto v___jp_2519_;
}
}
else
{
goto v___jp_2519_;
}
}
else
{
goto v___jp_2522_;
}
}
else
{
goto v___jp_2522_;
}
v___jp_2515_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2517_ = l_Lean_Parser_ParserState_next(v_s_2498_, v_c_2497_, v_i_2514_);
v___x_2518_ = l_Lean_Parser_hexNumberFn(v_pos_2502_, v_includeWhitespace_2496_, v___x_2516_, v_c_2497_, v___x_2517_);
return v___x_2518_;
}
v___jp_2519_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = l_Lean_Parser_ParserState_next(v_s_2498_, v_c_2497_, v_i_2514_);
v___x_2521_ = l_Lean_Parser_octalNumberFn(v_pos_2502_, v_includeWhitespace_2496_, v_c_2497_, v___x_2520_);
return v___x_2521_;
}
v___jp_2522_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = l_Lean_Parser_ParserState_next(v_s_2498_, v_c_2497_, v_i_2514_);
v___x_2524_ = l_Lean_Parser_binNumberFn(v_pos_2502_, v_includeWhitespace_2496_, v_c_2497_, v___x_2523_);
return v___x_2524_;
}
}
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec_ref(v_c_2497_);
v___x_2540_ = lean_box(0);
v___x_2541_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2498_, v___x_2540_);
return v___x_2541_;
}
v___jp_2499_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2501_ = l_Lean_Parser_ParserState_mkError(v_s_2498_, v___x_2500_);
return v___x_2501_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_numberFnAux_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeWhitespace_2496_ = stack[0].m_num;
lean_object* v_c_2497_ = stack[1].m_obj;
lean_object* v_s_2498_ = stack[2].m_obj;
lean_object* v_res_2542_;
v_res_2542_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_2496_, v_c_2497_, v_s_2498_);
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2543_, lean_object* v_c_2544_, lean_object* v_s_2545_){
_start:
{
uint8_t v_includeWhitespace_boxed_2546_; lean_object* v_res_2547_; 
v_includeWhitespace_boxed_2546_ = lean_unbox(v_includeWhitespace_2543_);
v_res_2547_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2546_, v_c_2544_, v_s_2545_);
return v_res_2547_;
}
}
uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2548_, lean_object* v_s_2549_){
_start:
{
lean_object* v_toInputContext_2550_; lean_object* v_pos_2551_; lean_object* v_inputString_2552_; uint32_t v_curr_2553_; uint32_t v___x_2554_; uint8_t v___x_2555_; 
v_toInputContext_2550_ = lean_ctor_get(v_c_2548_, 0);
v_pos_2551_ = lean_ctor_get(v_s_2549_, 2);
v_inputString_2552_ = lean_ctor_get(v_toInputContext_2550_, 0);
v_curr_2553_ = lean_string_utf8_get(v_inputString_2552_, v_pos_2551_);
v___x_2554_ = 46;
v___x_2555_ = lean_uint32_dec_eq(v_curr_2553_, v___x_2554_);
if (v___x_2555_ == 0)
{
return v___x_2555_;
}
else
{
lean_object* v_i_2556_; uint8_t v___x_2557_; 
v_i_2556_ = lean_string_utf8_next(v_inputString_2552_, v_pos_2551_);
v___x_2557_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2550_, v_i_2556_);
if (v___x_2557_ == 0)
{
uint32_t v_curr_2558_; uint32_t v___x_2570_; uint8_t v___x_2571_; 
v_curr_2558_ = lean_string_utf8_get(v_inputString_2552_, v_i_2556_);
lean_dec(v_i_2556_);
v___x_2570_ = 65;
v___x_2571_ = lean_uint32_dec_le(v___x_2570_, v_curr_2558_);
if (v___x_2571_ == 0)
{
goto v___jp_2565_;
}
else
{
uint32_t v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = 90;
v___x_2573_ = lean_uint32_dec_le(v_curr_2558_, v___x_2572_);
if (v___x_2573_ == 0)
{
goto v___jp_2565_;
}
else
{
return v___x_2555_;
}
}
v___jp_2559_:
{
uint32_t v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = 95;
v___x_2561_ = lean_uint32_dec_eq(v_curr_2558_, v___x_2560_);
if (v___x_2561_ == 0)
{
uint8_t v___x_2562_; 
v___x_2562_ = l_Lean_isLetterLike(v_curr_2558_);
if (v___x_2562_ == 0)
{
uint32_t v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = l_Lean_idBeginEscape;
v___x_2564_ = lean_uint32_dec_eq(v_curr_2558_, v___x_2563_);
return v___x_2564_;
}
else
{
return v___x_2555_;
}
}
else
{
return v___x_2555_;
}
}
v___jp_2565_:
{
uint32_t v___x_2566_; uint8_t v___x_2567_; 
v___x_2566_ = 97;
v___x_2567_ = lean_uint32_dec_le(v___x_2566_, v_curr_2558_);
if (v___x_2567_ == 0)
{
goto v___jp_2559_;
}
else
{
uint32_t v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = 122;
v___x_2569_ = lean_uint32_dec_le(v_curr_2558_, v___x_2568_);
if (v___x_2569_ == 0)
{
goto v___jp_2559_;
}
else
{
return v___x_2555_;
}
}
}
}
else
{
uint8_t v___x_2574_; 
lean_dec(v_i_2556_);
v___x_2574_ = 0;
return v___x_2574_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_isIdCont_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2548_ = stack[0].m_obj;
lean_object* v_s_2549_ = stack[1].m_obj;
uint8_t v_res_2575_;
v_res_2575_ = l_Lean_Parser_isIdCont(v_c_2548_, v_s_2549_);
stack->m_num = v_res_2575_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2576_, lean_object* v_s_2577_){
_start:
{
uint8_t v_res_2578_; lean_object* v_r_2579_; 
v_res_2578_ = l_Lean_Parser_isIdCont(v_c_2576_, v_s_2577_);
lean_dec_ref(v_s_2577_);
lean_dec_ref(v_c_2576_);
v_r_2579_ = lean_box(v_res_2578_);
return v_r_2579_;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2580_, lean_object* v_idStopPos_2581_, lean_object* v_tk_2582_){
_start:
{
if (lean_obj_tag(v_tk_2582_) == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = 0;
return v___x_2583_;
}
else
{
lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_val_2584_ = lean_ctor_get(v_tk_2582_, 0);
v___x_2585_ = lean_nat_sub(v_idStopPos_2581_, v_idStartPos_2580_);
v___x_2586_ = lean_string_utf8_byte_size(v_val_2584_);
v___x_2587_ = lean_nat_dec_le(v___x_2585_, v___x_2586_);
lean_dec(v___x_2585_);
return v___x_2587_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_isToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_idStartPos_2580_ = stack[0].m_obj;
lean_object* v_idStopPos_2581_ = stack[1].m_obj;
lean_object* v_tk_2582_ = stack[2].m_obj;
uint8_t v_res_2588_;
v_res_2588_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2580_, v_idStopPos_2581_, v_tk_2582_);
stack->m_num = v_res_2588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2589_, lean_object* v_idStopPos_2590_, lean_object* v_tk_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2589_, v_idStopPos_2590_, v_tk_2591_);
lean_dec(v_tk_2591_);
lean_dec(v_idStopPos_2590_);
lean_dec(v_idStartPos_2589_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object* v_a_2594_, lean_object* v_as_2595_, size_t v_i_2596_, size_t v_stop_2597_){
_start:
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_usize_dec_eq(v_i_2596_, v_stop_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = lean_array_uget_borrowed(v_as_2595_, v_i_2596_);
v___x_2600_ = lean_string_dec_eq(v_a_2594_, v___x_2599_);
if (v___x_2600_ == 0)
{
size_t v___x_2601_; size_t v___x_2602_; 
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2596_, v___x_2601_);
v_i_2596_ = v___x_2602_;
goto _start;
}
else
{
return v___x_2600_;
}
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = 0;
return v___x_2604_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2594_ = stack[0].m_obj;
lean_object* v_as_2595_ = stack[1].m_obj;
size_t v_i_2596_ = stack[2].m_num;
size_t v_stop_2597_ = stack[3].m_num;
uint8_t v_res_2605_;
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2594_, v_as_2595_, v_i_2596_, v_stop_2597_);
stack->m_num = v_res_2605_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object* v_a_2606_, lean_object* v_as_2607_, lean_object* v_i_2608_, lean_object* v_stop_2609_){
_start:
{
size_t v_i_boxed_2610_; size_t v_stop_boxed_2611_; uint8_t v_res_2612_; lean_object* v_r_2613_; 
v_i_boxed_2610_ = lean_unbox_usize(v_i_2608_);
lean_dec(v_i_2608_);
v_stop_boxed_2611_ = lean_unbox_usize(v_stop_2609_);
lean_dec(v_stop_2609_);
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2606_, v_as_2607_, v_i_boxed_2610_, v_stop_boxed_2611_);
lean_dec_ref(v_as_2607_);
lean_dec_ref(v_a_2606_);
v_r_2613_ = lean_box(v_res_2612_);
return v_r_2613_;
}
}
uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_as_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_array_get_size(v_as_2614_);
v___x_2618_ = lean_nat_dec_lt(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
return v___x_2618_;
}
else
{
if (v___x_2618_ == 0)
{
return v___x_2618_;
}
else
{
size_t v___x_2619_; size_t v___x_2620_; uint8_t v___x_2621_; 
v___x_2619_ = ((size_t)0ULL);
v___x_2620_ = lean_usize_of_nat(v___x_2617_);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2615_, v_as_2614_, v___x_2619_, v___x_2620_);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2614_ = stack[0].m_obj;
lean_object* v_a_2615_ = stack[1].m_obj;
uint8_t v_res_2622_;
v_res_2622_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2614_, v_a_2615_);
stack->m_num = v_res_2622_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_as_2623_, lean_object* v_a_2624_){
_start:
{
uint8_t v_res_2625_; lean_object* v_r_2626_; 
v_res_2625_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2623_, v_a_2624_);
lean_dec_ref(v_a_2624_);
lean_dec_ref(v_as_2623_);
v_r_2626_ = lean_box(v_res_2625_);
return v_r_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2629_, lean_object* v_tk_2630_, lean_object* v_c_2631_, lean_object* v_s_2632_){
_start:
{
if (lean_obj_tag(v_tk_2630_) == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v_c_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2634_ = lean_box(0);
v___x_2635_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2632_, v___x_2633_, v_startPos_2629_, v___x_2634_);
return v___x_2635_;
}
else
{
lean_object* v_toCacheableParserContext_2636_; lean_object* v_val_2637_; lean_object* v_toInputContext_2638_; lean_object* v_forbiddenTks_2639_; uint8_t v___x_2640_; 
v_toCacheableParserContext_2636_ = lean_ctor_get(v_c_2631_, 2);
v_val_2637_ = lean_ctor_get(v_tk_2630_, 0);
v_toInputContext_2638_ = lean_ctor_get(v_c_2631_, 0);
lean_inc_ref(v_toInputContext_2638_);
v_forbiddenTks_2639_ = lean_ctor_get(v_toCacheableParserContext_2636_, 3);
v___x_2640_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_2639_, v_val_2637_);
if (v___x_2640_ == 0)
{
lean_object* v_leading_2641_; lean_object* v___x_2642_; lean_object* v_stopPos_2643_; lean_object* v_s_2644_; lean_object* v_s_2645_; lean_object* v___y_2647_; lean_object* v_pos_2651_; lean_object* v_inputString_2652_; lean_object* v_endPos_2653_; uint8_t v___x_2654_; 
lean_inc(v_startPos_2629_);
v_leading_2641_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2631_, v_startPos_2629_);
v___x_2642_ = lean_string_utf8_byte_size(v_val_2637_);
v_stopPos_2643_ = lean_nat_add(v_startPos_2629_, v___x_2642_);
lean_inc(v_stopPos_2643_);
v_s_2644_ = l_Lean_Parser_ParserState_setPos(v_s_2632_, v_stopPos_2643_);
v_s_2645_ = l_Lean_Parser_whitespace(v_c_2631_, v_s_2644_);
v_pos_2651_ = lean_ctor_get(v_s_2645_, 2);
v_inputString_2652_ = lean_ctor_get(v_toInputContext_2638_, 0);
lean_inc_ref(v_inputString_2652_);
v_endPos_2653_ = lean_ctor_get(v_toInputContext_2638_, 3);
lean_inc(v_endPos_2653_);
lean_dec_ref(v_toInputContext_2638_);
v___x_2654_ = lean_nat_dec_le(v_pos_2651_, v_endPos_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_inc(v_stopPos_2643_);
v___x_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2655_, 0, v_inputString_2652_);
lean_ctor_set(v___x_2655_, 1, v_stopPos_2643_);
lean_ctor_set(v___x_2655_, 2, v_endPos_2653_);
v___y_2647_ = v___x_2655_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2656_; 
lean_dec(v_endPos_2653_);
lean_inc(v_pos_2651_);
lean_inc(v_stopPos_2643_);
v___x_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2656_, 0, v_inputString_2652_);
lean_ctor_set(v___x_2656_, 1, v_stopPos_2643_);
lean_ctor_set(v___x_2656_, 2, v_pos_2651_);
v___y_2647_ = v___x_2656_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v_atom_2649_; lean_object* v___x_2650_; 
v___x_2648_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2648_, 0, v_leading_2641_);
lean_ctor_set(v___x_2648_, 1, v_startPos_2629_);
lean_ctor_set(v___x_2648_, 2, v___y_2647_);
lean_ctor_set(v___x_2648_, 3, v_stopPos_2643_);
lean_inc(v_val_2637_);
v_atom_2649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2649_, 0, v___x_2648_);
lean_ctor_set(v_atom_2649_, 1, v_val_2637_);
v___x_2650_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2645_, v_atom_2649_);
return v___x_2650_;
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v_toInputContext_2638_);
lean_dec_ref(v_c_2631_);
v___x_2657_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2658_ = lean_box(0);
v___x_2659_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2632_, v___x_2657_, v_startPos_2629_, v___x_2658_);
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2660_, lean_object* v_tk_2661_, lean_object* v_c_2662_, lean_object* v_s_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2660_, v_tk_2661_, v_c_2662_, v_s_2663_);
lean_dec(v_tk_2661_);
return v_res_2664_;
}
}
lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2665_, lean_object* v_tk_2666_, lean_object* v_val_2667_, uint8_t v_includeWhitespace_2668_, lean_object* v_c_2669_, lean_object* v_s_2670_){
_start:
{
lean_object* v_pos_2671_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; uint8_t v___x_2681_; 
v_pos_2671_ = lean_ctor_get(v_s_2670_, 2);
v___x_2681_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2665_, v_pos_2671_, v_tk_2666_);
if (v___x_2681_ == 0)
{
lean_object* v_toInputContext_2682_; lean_object* v_inputString_2683_; lean_object* v_endPos_2684_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v_pos_2688_; lean_object* v___y_2694_; uint8_t v___x_2697_; 
lean_inc(v_pos_2671_);
v_toInputContext_2682_ = lean_ctor_get(v_c_2669_, 0);
v_inputString_2683_ = lean_ctor_get(v_toInputContext_2682_, 0);
lean_inc_ref(v_inputString_2683_);
v_endPos_2684_ = lean_ctor_get(v_toInputContext_2682_, 3);
lean_inc(v_endPos_2684_);
v___x_2697_ = lean_nat_dec_le(v_pos_2671_, v_endPos_2684_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_inc(v_endPos_2684_);
lean_inc(v_startPos_2665_);
lean_inc_ref(v_inputString_2683_);
v___x_2698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2698_, 0, v_inputString_2683_);
lean_ctor_set(v___x_2698_, 1, v_startPos_2665_);
lean_ctor_set(v___x_2698_, 2, v_endPos_2684_);
v___y_2694_ = v___x_2698_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2699_; 
lean_inc(v_pos_2671_);
lean_inc(v_startPos_2665_);
lean_inc_ref(v_inputString_2683_);
v___x_2699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2699_, 0, v_inputString_2683_);
lean_ctor_set(v___x_2699_, 1, v_startPos_2665_);
lean_ctor_set(v___x_2699_, 2, v_pos_2671_);
v___y_2694_ = v___x_2699_;
goto v___jp_2693_;
}
v___jp_2685_:
{
lean_object* v_leading_2689_; uint8_t v___x_2690_; 
lean_inc(v_startPos_2665_);
v_leading_2689_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2669_, v_startPos_2665_);
lean_dec_ref(v_c_2669_);
v___x_2690_ = lean_nat_dec_le(v_pos_2688_, v_endPos_2684_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
lean_dec(v_pos_2688_);
lean_inc(v_pos_2671_);
v___x_2691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2691_, 0, v_inputString_2683_);
lean_ctor_set(v___x_2691_, 1, v_pos_2671_);
lean_ctor_set(v___x_2691_, 2, v_endPos_2684_);
v___y_2673_ = v___y_2686_;
v___y_2674_ = v_leading_2689_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___x_2691_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2692_; 
lean_dec(v_endPos_2684_);
lean_inc(v_pos_2671_);
v___x_2692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2692_, 0, v_inputString_2683_);
lean_ctor_set(v___x_2692_, 1, v_pos_2671_);
lean_ctor_set(v___x_2692_, 2, v_pos_2688_);
v___y_2673_ = v___y_2686_;
v___y_2674_ = v_leading_2689_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___x_2692_;
goto v___jp_2672_;
}
}
v___jp_2693_:
{
if (v_includeWhitespace_2668_ == 0)
{
lean_inc(v_pos_2671_);
v___y_2686_ = v___y_2694_;
v___y_2687_ = v_s_2670_;
v_pos_2688_ = v_pos_2671_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2695_; lean_object* v_pos_2696_; 
lean_inc_ref(v_c_2669_);
v___x_2695_ = l_Lean_Parser_whitespace(v_c_2669_, v_s_2670_);
v_pos_2696_ = lean_ctor_get(v___x_2695_, 2);
lean_inc(v_pos_2696_);
v___y_2686_ = v___y_2694_;
v___y_2687_ = v___x_2695_;
v_pos_2688_ = v_pos_2696_;
goto v___jp_2685_;
}
}
}
else
{
lean_object* v___x_2700_; 
lean_dec(v_val_2667_);
v___x_2700_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2665_, v_tk_2666_, v_c_2669_, v_s_2670_);
return v___x_2700_;
}
v___jp_2672_:
{
lean_object* v_info_2677_; lean_object* v___x_2678_; lean_object* v_atom_2679_; lean_object* v___x_2680_; 
v_info_2677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2677_, 0, v___y_2674_);
lean_ctor_set(v_info_2677_, 1, v_startPos_2665_);
lean_ctor_set(v_info_2677_, 2, v___y_2676_);
lean_ctor_set(v_info_2677_, 3, v_pos_2671_);
v___x_2678_ = lean_box(0);
v_atom_2679_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2679_, 0, v_info_2677_);
lean_ctor_set(v_atom_2679_, 1, v___y_2673_);
lean_ctor_set(v_atom_2679_, 2, v_val_2667_);
lean_ctor_set(v_atom_2679_, 3, v___x_2678_);
v___x_2680_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2675_, v_atom_2679_);
return v___x_2680_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkIdResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2665_ = stack[0].m_obj;
lean_object* v_tk_2666_ = stack[1].m_obj;
lean_object* v_val_2667_ = stack[2].m_obj;
uint8_t v_includeWhitespace_2668_ = stack[3].m_num;
lean_object* v_c_2669_ = stack[4].m_obj;
lean_object* v_s_2670_ = stack[5].m_obj;
lean_object* v_res_2701_;
v_res_2701_ = l_Lean_Parser_mkIdResult(v_startPos_2665_, v_tk_2666_, v_val_2667_, v_includeWhitespace_2668_, v_c_2669_, v_s_2670_);
stack->m_obj
 = v_res_2701_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2702_, lean_object* v_tk_2703_, lean_object* v_val_2704_, lean_object* v_includeWhitespace_2705_, lean_object* v_c_2706_, lean_object* v_s_2707_){
_start:
{
uint8_t v_includeWhitespace_boxed_2708_; lean_object* v_res_2709_; 
v_includeWhitespace_boxed_2708_ = lean_unbox(v_includeWhitespace_2705_);
v_res_2709_ = l_Lean_Parser_mkIdResult(v_startPos_2702_, v_tk_2703_, v_val_2704_, v_includeWhitespace_boxed_2708_, v_c_2706_, v_s_2707_);
lean_dec(v_tk_2703_);
return v_res_2709_;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2710_){
_start:
{
uint32_t v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = 65;
v___x_2733_ = lean_uint32_dec_le(v___x_2732_, v___y_2710_);
if (v___x_2733_ == 0)
{
goto v___jp_2727_;
}
else
{
uint32_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = 90;
v___x_2735_ = lean_uint32_dec_le(v___y_2710_, v___x_2734_);
if (v___x_2735_ == 0)
{
goto v___jp_2727_;
}
else
{
return v___x_2735_;
}
}
v___jp_2711_:
{
uint32_t v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = 95;
v___x_2713_ = lean_uint32_dec_eq(v___y_2710_, v___x_2712_);
if (v___x_2713_ == 0)
{
uint32_t v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = 39;
v___x_2715_ = lean_uint32_dec_eq(v___y_2710_, v___x_2714_);
if (v___x_2715_ == 0)
{
uint32_t v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = 33;
v___x_2717_ = lean_uint32_dec_eq(v___y_2710_, v___x_2716_);
if (v___x_2717_ == 0)
{
uint32_t v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = 63;
v___x_2719_ = lean_uint32_dec_eq(v___y_2710_, v___x_2718_);
if (v___x_2719_ == 0)
{
uint8_t v___x_2720_; 
v___x_2720_ = l_Lean_isLetterLike(v___y_2710_);
if (v___x_2720_ == 0)
{
uint8_t v___x_2721_; 
v___x_2721_ = l_Lean_isSubScriptAlnum(v___y_2710_);
return v___x_2721_;
}
else
{
return v___x_2720_;
}
}
else
{
return v___x_2719_;
}
}
else
{
return v___x_2717_;
}
}
else
{
return v___x_2715_;
}
}
else
{
return v___x_2713_;
}
}
v___jp_2722_:
{
uint32_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = 48;
v___x_2724_ = lean_uint32_dec_le(v___x_2723_, v___y_2710_);
if (v___x_2724_ == 0)
{
goto v___jp_2711_;
}
else
{
uint32_t v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = 57;
v___x_2726_ = lean_uint32_dec_le(v___y_2710_, v___x_2725_);
if (v___x_2726_ == 0)
{
goto v___jp_2711_;
}
else
{
return v___x_2726_;
}
}
}
v___jp_2727_:
{
uint32_t v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = 97;
v___x_2729_ = lean_uint32_dec_le(v___x_2728_, v___y_2710_);
if (v___x_2729_ == 0)
{
goto v___jp_2722_;
}
else
{
uint32_t v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = 122;
v___x_2731_ = lean_uint32_dec_le(v___y_2710_, v___x_2730_);
if (v___x_2731_ == 0)
{
goto v___jp_2722_;
}
else
{
return v___x_2731_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_2710_ = stack[0].m_num;
uint8_t v_res_2736_;
v_res_2736_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_2710_);
stack->m_num = v_res_2736_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2737_){
_start:
{
uint32_t v___y_274__boxed_2738_; uint8_t v_res_2739_; lean_object* v_r_2740_; 
v___y_274__boxed_2738_ = lean_unbox_uint32(v___y_2737_);
lean_dec(v___y_2737_);
v_res_2739_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_274__boxed_2738_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2741_){
_start:
{
uint32_t v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = l_Lean_idEndEscape;
v___x_2743_ = lean_uint32_dec_eq(v___y_2741_, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_2741_ = stack[0].m_num;
uint8_t v_res_2744_;
v_res_2744_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_2741_);
stack->m_num = v_res_2744_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2745_){
_start:
{
uint32_t v___y_354__boxed_2746_; uint8_t v_res_2747_; lean_object* v_r_2748_; 
v___y_354__boxed_2746_ = lean_unbox_uint32(v___y_2745_);
lean_dec(v___y_2745_);
v_res_2747_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_354__boxed_2746_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2752_, lean_object* v_tk_2753_, uint8_t v_includeWhitespace_2754_, lean_object* v_r_2755_, lean_object* v_c_2756_, lean_object* v_s_2757_){
_start:
{
lean_object* v_pos_2758_; lean_object* v_toInputContext_2759_; uint8_t v___x_2760_; 
v_pos_2758_ = lean_ctor_get(v_s_2757_, 2);
v_toInputContext_2759_ = lean_ctor_get(v_c_2756_, 0);
v___x_2760_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2759_, v_pos_2758_);
if (v___x_2760_ == 0)
{
lean_object* v_inputString_2761_; uint32_t v_curr_2762_; uint32_t v___x_2763_; uint8_t v___x_2764_; 
v_inputString_2761_ = lean_ctor_get(v_toInputContext_2759_, 0);
v_curr_2762_ = lean_string_utf8_get_fast(v_inputString_2761_, v_pos_2758_);
v___x_2763_ = l_Lean_idBeginEscape;
v___x_2764_ = lean_uint32_dec_eq(v_curr_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___f_2765_; uint32_t v___x_2786_; uint8_t v___x_2787_; 
v___f_2765_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2786_ = 65;
v___x_2787_ = lean_uint32_dec_le(v___x_2786_, v_curr_2762_);
if (v___x_2787_ == 0)
{
goto v___jp_2781_;
}
else
{
uint32_t v___x_2788_; uint8_t v___x_2789_; 
v___x_2788_ = 90;
v___x_2789_ = lean_uint32_dec_le(v_curr_2762_, v___x_2788_);
if (v___x_2789_ == 0)
{
goto v___jp_2781_;
}
else
{
lean_inc(v_pos_2758_);
goto v___jp_2766_;
}
}
v___jp_2766_:
{
lean_object* v___x_2767_; lean_object* v_s_2768_; lean_object* v_pos_2769_; lean_object* v___x_2770_; lean_object* v_r_2771_; uint8_t v___x_2772_; 
v___x_2767_ = l_Lean_Parser_ParserState_next(v_s_2757_, v_c_2756_, v_pos_2758_);
v_s_2768_ = l_Lean_Parser_takeWhileFn(v___f_2765_, v_c_2756_, v___x_2767_);
v_pos_2769_ = lean_ctor_get(v_s_2768_, 2);
v___x_2770_ = lean_string_utf8_extract(v_inputString_2761_, v_pos_2758_, v_pos_2769_);
lean_dec(v_pos_2758_);
v_r_2771_ = l_Lean_Name_str___override(v_r_2755_, v___x_2770_);
v___x_2772_ = l_Lean_Parser_isIdCont(v_c_2756_, v_s_2768_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Parser_mkIdResult(v_startPos_2752_, v_tk_2753_, v_r_2771_, v_includeWhitespace_2754_, v_c_2756_, v_s_2768_);
return v___x_2773_;
}
else
{
lean_object* v_s_2774_; 
lean_inc(v_pos_2769_);
v_s_2774_ = l_Lean_Parser_ParserState_next(v_s_2768_, v_c_2756_, v_pos_2769_);
lean_dec(v_pos_2769_);
v_r_2755_ = v_r_2771_;
v_s_2757_ = v_s_2774_;
goto _start;
}
}
v___jp_2776_:
{
uint32_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = 95;
v___x_2778_ = lean_uint32_dec_eq(v_curr_2762_, v___x_2777_);
if (v___x_2778_ == 0)
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Lean_isLetterLike(v_curr_2762_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec(v_r_2755_);
v___x_2780_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2752_, v_tk_2753_, v_c_2756_, v_s_2757_);
return v___x_2780_;
}
else
{
lean_inc(v_pos_2758_);
goto v___jp_2766_;
}
}
else
{
lean_inc(v_pos_2758_);
goto v___jp_2766_;
}
}
v___jp_2781_:
{
uint32_t v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = 97;
v___x_2783_ = lean_uint32_dec_le(v___x_2782_, v_curr_2762_);
if (v___x_2783_ == 0)
{
goto v___jp_2776_;
}
else
{
uint32_t v___x_2784_; uint8_t v___x_2785_; 
v___x_2784_ = 122;
v___x_2785_ = lean_uint32_dec_le(v_curr_2762_, v___x_2784_);
if (v___x_2785_ == 0)
{
goto v___jp_2776_;
}
else
{
lean_inc(v_pos_2758_);
goto v___jp_2766_;
}
}
}
}
else
{
lean_object* v___f_2790_; lean_object* v_startPart_2791_; lean_object* v___x_2792_; lean_object* v_s_2793_; lean_object* v_pos_2794_; uint8_t v___x_2795_; 
v___f_2790_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2791_ = lean_string_utf8_next_fast(v_inputString_2761_, v_pos_2758_);
v___x_2792_ = l_Lean_Parser_ParserState_setPos(v_s_2757_, v_startPart_2791_);
v_s_2793_ = l_Lean_Parser_takeUntilFn(v___f_2790_, v_c_2756_, v___x_2792_);
v_pos_2794_ = lean_ctor_get(v_s_2793_, 2);
v___x_2795_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2759_, v_pos_2794_);
if (v___x_2795_ == 0)
{
lean_object* v_s_2796_; lean_object* v___x_2797_; lean_object* v_r_2798_; uint8_t v___x_2799_; 
lean_inc(v_pos_2794_);
v_s_2796_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2793_, v_c_2756_, v_pos_2794_);
v___x_2797_ = lean_string_utf8_extract(v_inputString_2761_, v_startPart_2791_, v_pos_2794_);
lean_dec(v_pos_2794_);
v_r_2798_ = l_Lean_Name_str___override(v_r_2755_, v___x_2797_);
v___x_2799_ = l_Lean_Parser_isIdCont(v_c_2756_, v_s_2796_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Parser_mkIdResult(v_startPos_2752_, v_tk_2753_, v_r_2798_, v_includeWhitespace_2754_, v_c_2756_, v_s_2796_);
return v___x_2800_;
}
else
{
lean_object* v_pos_2801_; lean_object* v_s_2802_; 
v_pos_2801_ = lean_ctor_get(v_s_2796_, 2);
lean_inc(v_pos_2801_);
v_s_2802_ = l_Lean_Parser_ParserState_next(v_s_2796_, v_c_2756_, v_pos_2801_);
lean_dec(v_pos_2801_);
v_r_2755_ = v_r_2798_;
v_s_2757_ = v_s_2802_;
goto _start;
}
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec_ref(v_c_2756_);
lean_dec(v_r_2755_);
lean_dec(v_startPos_2752_);
v___x_2804_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2805_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2793_, v___x_2804_, v_startPart_2791_);
return v___x_2805_;
}
}
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec_ref(v_c_2756_);
lean_dec(v_r_2755_);
lean_dec(v_startPos_2752_);
v___x_2806_ = lean_box(0);
v___x_2807_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2757_, v___x_2806_);
return v___x_2807_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2752_ = stack[0].m_obj;
lean_object* v_tk_2753_ = stack[1].m_obj;
uint8_t v_includeWhitespace_2754_ = stack[2].m_num;
lean_object* v_r_2755_ = stack[3].m_obj;
lean_object* v_c_2756_ = stack[4].m_obj;
lean_object* v_s_2757_ = stack[5].m_obj;
lean_object* v_res_2808_;
v_res_2808_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2752_, v_tk_2753_, v_includeWhitespace_2754_, v_r_2755_, v_c_2756_, v_s_2757_);
stack->m_obj
 = v_res_2808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2809_, lean_object* v_tk_2810_, lean_object* v_includeWhitespace_2811_, lean_object* v_r_2812_, lean_object* v_c_2813_, lean_object* v_s_2814_){
_start:
{
uint8_t v_includeWhitespace_boxed_2815_; lean_object* v_res_2816_; 
v_includeWhitespace_boxed_2815_ = lean_unbox(v_includeWhitespace_2811_);
v_res_2816_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2809_, v_tk_2810_, v_includeWhitespace_boxed_2815_, v_r_2812_, v_c_2813_, v_s_2814_);
lean_dec(v_tk_2810_);
return v_res_2816_;
}
}
lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2817_, lean_object* v_tk_2818_, lean_object* v_r_2819_, uint8_t v_includeWhitespace_2820_, lean_object* v_c_2821_, lean_object* v_s_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2817_, v_tk_2818_, v_includeWhitespace_2820_, v_r_2819_, v_c_2821_, v_s_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT void l_Lean_Parser_identFnAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_2817_ = stack[0].m_obj;
lean_object* v_tk_2818_ = stack[1].m_obj;
lean_object* v_r_2819_ = stack[2].m_obj;
uint8_t v_includeWhitespace_2820_ = stack[3].m_num;
lean_object* v_c_2821_ = stack[4].m_obj;
lean_object* v_s_2822_ = stack[5].m_obj;
lean_object* v_res_2824_;
v_res_2824_ = l_Lean_Parser_identFnAux(v_startPos_2817_, v_tk_2818_, v_r_2819_, v_includeWhitespace_2820_, v_c_2821_, v_s_2822_);
stack->m_obj
 = v_res_2824_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2825_, lean_object* v_tk_2826_, lean_object* v_r_2827_, lean_object* v_includeWhitespace_2828_, lean_object* v_c_2829_, lean_object* v_s_2830_){
_start:
{
uint8_t v_includeWhitespace_boxed_2831_; lean_object* v_res_2832_; 
v_includeWhitespace_boxed_2831_ = lean_unbox(v_includeWhitespace_2828_);
v_res_2832_ = l_Lean_Parser_identFnAux(v_startPos_2825_, v_tk_2826_, v_r_2827_, v_includeWhitespace_boxed_2831_, v_c_2829_, v_s_2830_);
lean_dec(v_tk_2826_);
return v_res_2832_;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2833_){
_start:
{
uint32_t v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = 65;
v___x_2846_ = lean_uint32_dec_le(v___x_2845_, v_c_2833_);
if (v___x_2846_ == 0)
{
goto v___jp_2840_;
}
else
{
uint32_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = 90;
v___x_2848_ = lean_uint32_dec_le(v_c_2833_, v___x_2847_);
if (v___x_2848_ == 0)
{
goto v___jp_2840_;
}
else
{
return v___x_2848_;
}
}
v___jp_2834_:
{
uint32_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = 95;
v___x_2836_ = lean_uint32_dec_eq(v_c_2833_, v___x_2835_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_isLetterLike(v_c_2833_);
if (v___x_2837_ == 0)
{
uint32_t v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = l_Lean_idBeginEscape;
v___x_2839_ = lean_uint32_dec_eq(v_c_2833_, v___x_2838_);
return v___x_2839_;
}
else
{
return v___x_2837_;
}
}
else
{
return v___x_2836_;
}
}
v___jp_2840_:
{
uint32_t v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = 97;
v___x_2842_ = lean_uint32_dec_le(v___x_2841_, v_c_2833_);
if (v___x_2842_ == 0)
{
goto v___jp_2834_;
}
else
{
uint32_t v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = 122;
v___x_2844_ = lean_uint32_dec_le(v_c_2833_, v___x_2843_);
if (v___x_2844_ == 0)
{
goto v___jp_2834_;
}
else
{
return v___x_2844_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_2833_ = stack[0].m_num;
uint8_t v_res_2849_;
v_res_2849_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_2833_);
stack->m_num = v_res_2849_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2850_){
_start:
{
uint32_t v_c_boxed_2851_; uint8_t v_res_2852_; lean_object* v_r_2853_; 
v_c_boxed_2851_ = lean_unbox_uint32(v_c_2850_);
lean_dec(v_c_2850_);
v_res_2852_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2851_);
v_r_2853_ = lean_box(v_res_2852_);
return v_r_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2855_, lean_object* v_c_2856_, lean_object* v_s_2857_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v_s_2862_; lean_object* v_stxStack_2863_; lean_object* v_errorMsg_2864_; uint8_t v___x_2865_; 
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_box(0);
v___x_2860_ = 1;
v___x_2861_ = l_Lean_Parser_ParserState_next(v_s_2857_, v_c_2856_, v_startPos_2855_);
v_s_2862_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2855_, v___x_2858_, v___x_2860_, v___x_2859_, v_c_2856_, v___x_2861_);
v_stxStack_2863_ = lean_ctor_get(v_s_2862_, 0);
v_errorMsg_2864_ = lean_ctor_get(v_s_2862_, 4);
v___x_2865_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2864_, v___x_2858_);
if (v___x_2865_ == 0)
{
return v_s_2862_;
}
else
{
lean_object* v_stx_2866_; 
v_stx_2866_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2863_);
if (lean_obj_tag(v_stx_2866_) == 3)
{
lean_object* v_rawVal_2867_; lean_object* v_info_2868_; lean_object* v_str_2869_; lean_object* v_startPos_2870_; lean_object* v_stopPos_2871_; lean_object* v_s_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_rawVal_2867_ = lean_ctor_get(v_stx_2866_, 1);
lean_inc_ref(v_rawVal_2867_);
v_info_2868_ = lean_ctor_get(v_stx_2866_, 0);
lean_inc(v_info_2868_);
lean_dec_ref_known(v_stx_2866_, 4);
v_str_2869_ = lean_ctor_get(v_rawVal_2867_, 0);
lean_inc_ref(v_str_2869_);
v_startPos_2870_ = lean_ctor_get(v_rawVal_2867_, 1);
lean_inc(v_startPos_2870_);
v_stopPos_2871_ = lean_ctor_get(v_rawVal_2867_, 2);
lean_inc(v_stopPos_2871_);
lean_dec_ref(v_rawVal_2867_);
v_s_2872_ = l_Lean_Parser_ParserState_popSyntax(v_s_2862_);
v___x_2873_ = lean_string_utf8_extract(v_str_2869_, v_startPos_2870_, v_stopPos_2871_);
lean_dec(v_stopPos_2871_);
lean_dec(v_startPos_2870_);
lean_dec_ref(v_str_2869_);
v___x_2874_ = l_Lean_Syntax_mkNameLit(v___x_2873_, v_info_2868_);
v___x_2875_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2872_, v___x_2874_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v_stx_2866_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2877_ = l_Lean_Parser_ParserState_mkError(v_s_2862_, v___x_2876_);
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2878_, lean_object* v_s_2879_){
_start:
{
lean_object* v_toInputContext_2880_; lean_object* v_pos_2881_; lean_object* v_tokens_2882_; lean_object* v_inputString_2883_; lean_object* v_endPos_2884_; uint32_t v_curr_2885_; uint32_t v___x_2886_; uint8_t v___x_2887_; uint8_t v___x_2888_; 
v_toInputContext_2880_ = lean_ctor_get(v_c_2878_, 0);
v_pos_2881_ = lean_ctor_get(v_s_2879_, 2);
v_tokens_2882_ = lean_ctor_get(v_c_2878_, 3);
v_inputString_2883_ = lean_ctor_get(v_toInputContext_2880_, 0);
v_endPos_2884_ = lean_ctor_get(v_toInputContext_2880_, 3);
v_curr_2885_ = lean_string_utf8_get(v_inputString_2883_, v_pos_2881_);
v___x_2886_ = 34;
v___x_2887_ = lean_uint32_dec_eq(v_curr_2885_, v___x_2886_);
v___x_2888_ = 1;
if (v___x_2887_ == 0)
{
uint32_t v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = 39;
v___x_2914_ = lean_uint32_dec_eq(v_curr_2885_, v___x_2913_);
if (v___x_2914_ == 0)
{
goto v___jp_2907_;
}
else
{
lean_object* v___x_2915_; uint32_t v___x_2916_; uint8_t v___x_2917_; 
v___x_2915_ = lean_string_utf8_next(v_inputString_2883_, v_pos_2881_);
v___x_2916_ = lean_string_utf8_get(v_inputString_2883_, v___x_2915_);
lean_dec(v___x_2915_);
v___x_2917_ = lean_uint32_dec_eq(v___x_2916_, v___x_2913_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_inc(v_pos_2881_);
v___x_2918_ = l_Lean_Parser_ParserState_next(v_s_2879_, v_c_2878_, v_pos_2881_);
v___x_2919_ = l_Lean_Parser_charLitFnAux(v_pos_2881_, v_c_2878_, v___x_2918_);
return v___x_2919_;
}
else
{
goto v___jp_2907_;
}
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_inc(v_pos_2881_);
v___x_2920_ = l_Lean_Parser_ParserState_next(v_s_2879_, v_c_2878_, v_pos_2881_);
v___x_2921_ = l_Lean_Parser_strLitFnAux(v_pos_2881_, v___x_2888_, v_c_2878_, v___x_2920_);
return v___x_2921_;
}
v___jp_2889_:
{
lean_object* v_tk_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_inc(v_pos_2881_);
v_tk_2890_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2883_, v_tokens_2882_, v_pos_2881_, v_endPos_2884_);
v___x_2891_ = lean_box(0);
v___x_2892_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2881_, v_tk_2890_, v___x_2888_, v___x_2891_, v_c_2878_, v_s_2879_);
lean_dec(v_tk_2890_);
return v___x_2892_;
}
v___jp_2893_:
{
uint32_t v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = 114;
v___x_2895_ = lean_uint32_dec_eq(v_curr_2885_, v___x_2894_);
if (v___x_2895_ == 0)
{
goto v___jp_2889_;
}
else
{
lean_object* v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = lean_string_utf8_next(v_inputString_2883_, v_pos_2881_);
v___x_2897_ = l_Lean_Parser_isRawStrLitStart(v_c_2878_, v___x_2896_);
if (v___x_2897_ == 0)
{
goto v___jp_2889_;
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_Lean_Parser_ParserState_next(v_s_2879_, v_c_2878_, v_pos_2881_);
v___x_2899_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2881_, v_c_2878_, v___x_2898_);
return v___x_2899_;
}
}
}
v___jp_2900_:
{
uint32_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 96;
v___x_2902_ = lean_uint32_dec_eq(v_curr_2885_, v___x_2901_);
if (v___x_2902_ == 0)
{
goto v___jp_2893_;
}
else
{
lean_object* v___x_2903_; uint32_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = lean_string_utf8_next(v_inputString_2883_, v_pos_2881_);
v___x_2904_ = lean_string_utf8_get(v_inputString_2883_, v___x_2903_);
lean_dec(v___x_2903_);
v___x_2905_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2904_);
if (v___x_2905_ == 0)
{
goto v___jp_2893_;
}
else
{
lean_object* v___x_2906_; 
v___x_2906_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2881_, v_c_2878_, v_s_2879_);
return v___x_2906_;
}
}
}
v___jp_2907_:
{
uint32_t v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = 48;
v___x_2909_ = lean_uint32_dec_le(v___x_2908_, v_curr_2885_);
if (v___x_2909_ == 0)
{
lean_inc(v_pos_2881_);
goto v___jp_2900_;
}
else
{
uint32_t v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = 57;
v___x_2911_ = lean_uint32_dec_le(v_curr_2885_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_inc(v_pos_2881_);
goto v___jp_2900_;
}
else
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Parser_numberFnAux(v___x_2888_, v_c_2878_, v_s_2879_);
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2922_, lean_object* v_s_2923_){
_start:
{
lean_object* v_cache_2924_; lean_object* v_errorMsg_2925_; 
v_cache_2924_ = lean_ctor_get(v_s_2923_, 3);
lean_inc_ref(v_cache_2924_);
v_errorMsg_2925_ = lean_ctor_get(v_s_2923_, 4);
if (lean_obj_tag(v_errorMsg_2925_) == 0)
{
lean_object* v_stxStack_2926_; lean_object* v_lhsPrec_2927_; lean_object* v_pos_2928_; lean_object* v_recoveredErrors_2929_; lean_object* v_parserCache_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2955_; 
v_stxStack_2926_ = lean_ctor_get(v_s_2923_, 0);
v_lhsPrec_2927_ = lean_ctor_get(v_s_2923_, 1);
v_pos_2928_ = lean_ctor_get(v_s_2923_, 2);
v_recoveredErrors_2929_ = lean_ctor_get(v_s_2923_, 5);
v_parserCache_2930_ = lean_ctor_get(v_cache_2924_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_cache_2924_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v_cache_2924_, 0);
lean_dec(v_unused_2956_);
v___x_2932_ = v_cache_2924_;
v_isShared_2933_ = v_isSharedCheck_2955_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_parserCache_2930_);
lean_dec(v_cache_2924_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2955_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2926_);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_nat_dec_eq(v___x_2934_, v___x_2935_);
lean_dec(v___x_2934_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2948_; 
lean_inc_ref(v_recoveredErrors_2929_);
lean_inc(v_pos_2928_);
lean_inc(v_lhsPrec_2927_);
lean_inc_ref(v_stxStack_2926_);
lean_inc(v_errorMsg_2925_);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_s_2923_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; lean_object* v_unused_2951_; lean_object* v_unused_2952_; lean_object* v_unused_2953_; lean_object* v_unused_2954_; 
v_unused_2949_ = lean_ctor_get(v_s_2923_, 5);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_s_2923_, 4);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_s_2923_, 3);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v_s_2923_, 2);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_s_2923_, 1);
lean_dec(v_unused_2953_);
v_unused_2954_ = lean_ctor_get(v_s_2923_, 0);
lean_dec(v_unused_2954_);
v___x_2938_ = v_s_2923_;
v_isShared_2939_ = v_isSharedCheck_2948_;
goto v_resetjp_2937_;
}
else
{
lean_dec(v_s_2923_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2948_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v_tk_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v_tk_2940_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2926_);
lean_inc(v_pos_2928_);
v___x_2941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2941_, 0, v_startPos_2922_);
lean_ctor_set(v___x_2941_, 1, v_pos_2928_);
lean_ctor_set(v___x_2941_, 2, v_tk_2940_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2941_);
v___x_2943_ = v___x_2932_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_parserCache_2930_);
v___x_2943_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 3, v___x_2943_);
v___x_2945_ = v___x_2938_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_stxStack_2926_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_lhsPrec_2927_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_pos_2928_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_errorMsg_2925_);
lean_ctor_set(v_reuseFailAlloc_2946_, 5, v_recoveredErrors_2929_);
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
else
{
lean_del_object(v___x_2932_);
lean_dec_ref(v_parserCache_2930_);
lean_dec(v_startPos_2922_);
return v_s_2923_;
}
}
}
else
{
lean_dec_ref(v_cache_2924_);
lean_dec(v_startPos_2922_);
return v_s_2923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2957_, lean_object* v_c_2958_, lean_object* v_s_2959_){
_start:
{
lean_object* v_pos_2960_; lean_object* v_cache_2961_; lean_object* v_toInputContext_2962_; uint8_t v___x_2963_; 
v_pos_2960_ = lean_ctor_get(v_s_2959_, 2);
v_cache_2961_ = lean_ctor_get(v_s_2959_, 3);
v_toInputContext_2962_ = lean_ctor_get(v_c_2958_, 0);
v___x_2963_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2962_, v_pos_2960_);
if (v___x_2963_ == 0)
{
lean_object* v_tokenCache_2964_; lean_object* v_startPos_2965_; lean_object* v_stopPos_2966_; lean_object* v_token_2967_; uint8_t v_decide_2968_; 
lean_dec(v_expected_2957_);
v_tokenCache_2964_ = lean_ctor_get(v_cache_2961_, 0);
v_startPos_2965_ = lean_ctor_get(v_tokenCache_2964_, 0);
v_stopPos_2966_ = lean_ctor_get(v_tokenCache_2964_, 1);
v_token_2967_ = lean_ctor_get(v_tokenCache_2964_, 2);
v_decide_2968_ = lean_nat_dec_eq(v_startPos_2965_, v_pos_2960_);
if (v_decide_2968_ == 0)
{
lean_object* v_s_2969_; lean_object* v___x_2970_; 
lean_inc(v_pos_2960_);
v_s_2969_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2958_, v_s_2959_);
v___x_2970_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2960_, v_s_2969_);
return v___x_2970_;
}
else
{
lean_object* v_s_2971_; lean_object* v___x_2972_; 
lean_inc(v_token_2967_);
lean_inc(v_stopPos_2966_);
lean_dec_ref(v_c_2958_);
v_s_2971_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2959_, v_token_2967_);
v___x_2972_ = l_Lean_Parser_ParserState_setPos(v_s_2971_, v_stopPos_2966_);
return v___x_2972_;
}
}
else
{
lean_object* v___x_2973_; 
lean_dec_ref(v_c_2958_);
v___x_2973_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2959_, v_expected_2957_);
return v___x_2973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2974_, lean_object* v_s_2975_){
_start:
{
lean_object* v_pos_2976_; lean_object* v_iniSz_2977_; lean_object* v___x_2978_; lean_object* v_s_2979_; lean_object* v_errorMsg_2980_; 
v_pos_2976_ = lean_ctor_get(v_s_2975_, 2);
lean_inc(v_pos_2976_);
v_iniSz_2977_ = l_Lean_Parser_ParserState_stackSize(v_s_2975_);
v___x_2978_ = lean_box(0);
v_s_2979_ = l_Lean_Parser_tokenFn(v___x_2978_, v_c_2974_, v_s_2975_);
v_errorMsg_2980_ = lean_ctor_get(v_s_2979_, 4);
lean_inc(v_errorMsg_2980_);
if (lean_obj_tag(v_errorMsg_2980_) == 1)
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2989_; 
v_isSharedCheck_2989_ = !lean_is_exclusive(v_errorMsg_2980_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_errorMsg_2980_, 0);
lean_dec(v_unused_2990_);
v___x_2982_ = v_errorMsg_2980_;
v_isShared_2983_ = v_isSharedCheck_2989_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v_errorMsg_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2989_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
lean_inc_ref(v_s_2979_);
v___x_2984_ = l_Lean_Parser_ParserState_restore(v_s_2979_, v_iniSz_2977_, v_pos_2976_);
lean_dec(v_iniSz_2977_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 0);
lean_ctor_set(v___x_2982_, 0, v_s_2979_);
v___x_2986_ = v___x_2982_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_s_2979_);
v___x_2986_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2984_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
return v___x_2987_;
}
}
}
else
{
lean_object* v_stxStack_2991_; lean_object* v_stx_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec(v_errorMsg_2980_);
v_stxStack_2991_ = lean_ctor_get(v_s_2979_, 0);
v_stx_2992_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2991_);
v___x_2993_ = l_Lean_Parser_ParserState_restore(v_s_2979_, v_iniSz_2977_, v_pos_2976_);
lean_dec(v_iniSz_2977_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_stx_2992_);
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2996_, lean_object* v_s_2997_){
_start:
{
lean_object* v_cache_2998_; lean_object* v_tokenCache_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3012_; 
v_cache_2998_ = lean_ctor_get(v_s_2997_, 3);
lean_inc_ref(v_cache_2998_);
v_tokenCache_2999_ = lean_ctor_get(v_cache_2998_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_cache_2998_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; 
v_unused_3013_ = lean_ctor_get(v_cache_2998_, 1);
lean_dec(v_unused_3013_);
v___x_3001_ = v_cache_2998_;
v_isShared_3002_ = v_isSharedCheck_3012_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_tokenCache_2999_);
lean_dec(v_cache_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3012_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_pos_3003_; lean_object* v_startPos_3004_; lean_object* v_token_3005_; uint8_t v_decide_3006_; 
v_pos_3003_ = lean_ctor_get(v_s_2997_, 2);
v_startPos_3004_ = lean_ctor_get(v_tokenCache_2999_, 0);
lean_inc(v_startPos_3004_);
v_token_3005_ = lean_ctor_get(v_tokenCache_2999_, 2);
lean_inc(v_token_3005_);
lean_dec_ref(v_tokenCache_2999_);
v_decide_3006_ = lean_nat_dec_eq(v_startPos_3004_, v_pos_3003_);
lean_dec(v_startPos_3004_);
if (v_decide_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec(v_token_3005_);
lean_del_object(v___x_3001_);
v___x_3007_ = l_Lean_Parser_peekTokenAux(v_c_2996_, v_s_2997_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
lean_dec_ref(v_c_2996_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_token_3005_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3008_);
lean_ctor_set(v___x_3001_, 0, v_s_2997_);
v___x_3010_ = v___x_3001_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_s_2997_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_3014_, lean_object* v_c_3015_, lean_object* v_s_3016_){
_start:
{
lean_object* v_pos_3017_; lean_object* v_toInputContext_3018_; uint8_t v___x_3019_; 
v_pos_3017_ = lean_ctor_get(v_s_3016_, 2);
v_toInputContext_3018_ = lean_ctor_get(v_c_3015_, 0);
v___x_3019_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3018_, v_pos_3017_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_inc(v_pos_3017_);
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_box(0);
v___x_3022_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_3017_, v___x_3020_, v_includeWhitespace_3014_, v___x_3021_, v_c_3015_, v_s_3016_);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
lean_dec_ref(v_c_3015_);
v___x_3023_ = lean_box(0);
v___x_3024_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3016_, v___x_3023_);
return v___x_3024_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_rawIdentFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeWhitespace_3014_ = stack[0].m_num;
lean_object* v_c_3015_ = stack[1].m_obj;
lean_object* v_s_3016_ = stack[2].m_obj;
lean_object* v_res_3025_;
v_res_3025_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_3014_, v_c_3015_, v_s_3016_);
stack->m_obj
 = v_res_3025_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_3026_, lean_object* v_c_3027_, lean_object* v_s_3028_){
_start:
{
uint8_t v_includeWhitespace_boxed_3029_; lean_object* v_res_3030_; 
v_includeWhitespace_boxed_3029_ = lean_unbox(v_includeWhitespace_3026_);
v_res_3030_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_3029_, v_c_3027_, v_s_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_3031_, lean_object* v_expected_3032_, lean_object* v_c_3033_, lean_object* v_s_3034_){
_start:
{
lean_object* v_pos_3035_; lean_object* v_s_3036_; lean_object* v_stxStack_3037_; lean_object* v_errorMsg_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_pos_3035_ = lean_ctor_get(v_s_3034_, 2);
lean_inc(v_pos_3035_);
lean_inc(v_expected_3032_);
v_s_3036_ = l_Lean_Parser_tokenFn(v_expected_3032_, v_c_3033_, v_s_3034_);
v_stxStack_3037_ = lean_ctor_get(v_s_3036_, 0);
v_errorMsg_3038_ = lean_ctor_get(v_s_3036_, 4);
v___x_3039_ = lean_box(0);
v___x_3040_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_dec(v_pos_3035_);
lean_dec(v_expected_3032_);
lean_dec_ref(v_p_3031_);
return v_s_3036_;
}
else
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3037_);
if (lean_obj_tag(v___x_3041_) == 2)
{
lean_object* v_val_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_val_3042_ = lean_ctor_get(v___x_3041_, 1);
lean_inc_ref(v_val_3042_);
lean_dec_ref_known(v___x_3041_, 2);
v___x_3043_ = lean_apply_1(v_p_3031_, v_val_3042_);
v___x_3044_ = lean_unbox(v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3036_, v_expected_3032_, v_pos_3035_);
return v___x_3045_;
}
else
{
lean_dec(v_pos_3035_);
lean_dec(v_expected_3032_);
return v_s_3036_;
}
}
else
{
lean_object* v___x_3046_; 
lean_dec(v___x_3041_);
lean_dec_ref(v_p_3031_);
v___x_3046_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3036_, v_expected_3032_, v_pos_3035_);
return v___x_3046_;
}
}
}
}
uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_3047_, lean_object* v_s_3048_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_string_dec_eq(v_s_3048_, v_sym_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT void l_Lean_Parser_symbolFnAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_3047_ = stack[0].m_obj;
lean_object* v_s_3048_ = stack[1].m_obj;
uint8_t v_res_3050_;
v_res_3050_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_3047_, v_s_3048_);
stack->m_num = v_res_3050_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_3051_, lean_object* v_s_3052_){
_start:
{
uint8_t v_res_3053_; lean_object* v_r_3054_; 
v_res_3053_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_3051_, v_s_3052_);
lean_dec_ref(v_s_3052_);
lean_dec_ref(v_sym_3051_);
v_r_3054_ = lean_box(v_res_3053_);
return v_r_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_3055_, lean_object* v_errorMsg_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3059_, 0, v_sym_3055_);
v___x_3060_ = lean_box(0);
v___x_3061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_errorMsg_3056_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Lean_Parser_satisfySymbolFn(v___f_3059_, v___x_3061_, v_a_3057_, v_a_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_3063_, lean_object* v_tks_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_sym_3063_);
lean_ctor_set(v___x_3065_, 1, v_tks_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_3066_){
_start:
{
lean_object* v___f_3067_; lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_inc_ref(v_sym_3066_);
v___f_3067_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_3067_, 0, v_sym_3066_);
v___f_3068_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_sym_3066_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3072_, 0, v___f_3067_);
lean_ctor_set(v___x_3072_, 1, v___f_3068_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3076_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3077_ = lean_string_append(v___x_3076_, v_sym_3073_);
v___x_3078_ = lean_string_append(v___x_3077_, v___x_3076_);
v___x_3079_ = l_Lean_Parser_symbolFnAux(v_sym_3073_, v___x_3078_, v_a_3074_, v_a_3075_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v_str_3085_; lean_object* v_startInclusive_3086_; lean_object* v_endExclusive_3087_; lean_object* v_sym_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_string_utf8_byte_size(v_sym_3080_);
v___x_3083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3083_, 0, v_sym_3080_);
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
v___x_3089_ = l_Lean_Parser_symbolInfo(v_sym_3088_);
v___x_3090_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3090_, 0, v_sym_3088_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3092_, lean_object* v_errorMsg_3093_, lean_object* v_c_3094_, lean_object* v_s_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v_s_3098_; lean_object* v_stxStack_3102_; lean_object* v_errorMsg_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3096_ = lean_box(0);
lean_inc_ref(v_errorMsg_3093_);
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_errorMsg_3093_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v_s_3098_ = l_Lean_Parser_tokenFn(v___x_3097_, v_c_3094_, v_s_3095_);
v_stxStack_3102_ = lean_ctor_get(v_s_3098_, 0);
v_errorMsg_3103_ = lean_ctor_get(v_s_3098_, 4);
v___x_3104_ = lean_box(0);
v___x_3105_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_dec_ref(v_errorMsg_3093_);
lean_dec_ref(v_sym_3092_);
return v_s_3098_;
}
else
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3102_);
switch(lean_obj_tag(v___x_3106_))
{
case 2:
{
lean_object* v_val_3107_; uint8_t v___x_3108_; 
v_val_3107_ = lean_ctor_get(v___x_3106_, 1);
lean_inc_ref(v_val_3107_);
lean_dec_ref_known(v___x_3106_, 2);
v___x_3108_ = lean_string_dec_eq(v_sym_3092_, v_val_3107_);
lean_dec_ref(v_val_3107_);
lean_dec_ref(v_sym_3092_);
if (v___x_3108_ == 0)
{
goto v___jp_3099_;
}
else
{
lean_dec_ref(v_errorMsg_3093_);
return v_s_3098_;
}
}
case 3:
{
lean_object* v_rawVal_3109_; lean_object* v_info_3110_; lean_object* v_str_3111_; lean_object* v_startPos_3112_; lean_object* v_stopPos_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v_rawVal_3109_ = lean_ctor_get(v___x_3106_, 1);
lean_inc_ref(v_rawVal_3109_);
v_info_3110_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_info_3110_);
lean_dec_ref_known(v___x_3106_, 4);
v_str_3111_ = lean_ctor_get(v_rawVal_3109_, 0);
lean_inc_ref(v_str_3111_);
v_startPos_3112_ = lean_ctor_get(v_rawVal_3109_, 1);
lean_inc(v_startPos_3112_);
v_stopPos_3113_ = lean_ctor_get(v_rawVal_3109_, 2);
lean_inc(v_stopPos_3113_);
lean_dec_ref(v_rawVal_3109_);
v___x_3114_ = lean_string_utf8_extract(v_str_3111_, v_startPos_3112_, v_stopPos_3113_);
lean_dec(v_stopPos_3113_);
lean_dec(v_startPos_3112_);
lean_dec_ref(v_str_3111_);
v___x_3115_ = lean_string_dec_eq(v_sym_3092_, v___x_3114_);
lean_dec_ref(v___x_3114_);
if (v___x_3115_ == 0)
{
lean_dec(v_info_3110_);
lean_dec_ref(v_sym_3092_);
goto v___jp_3099_;
}
else
{
lean_object* v_s_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v_errorMsg_3093_);
v_s_3116_ = l_Lean_Parser_ParserState_popSyntax(v_s_3098_);
v___x_3117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_info_3110_);
lean_ctor_set(v___x_3117_, 1, v_sym_3092_);
v___x_3118_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3116_, v___x_3117_);
return v___x_3118_;
}
}
default: 
{
lean_dec(v___x_3106_);
lean_dec_ref(v_sym_3092_);
goto v___jp_3099_;
}
}
}
v___jp_3099_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3098_, v_errorMsg_3093_, v___x_3100_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3122_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3123_ = lean_string_append(v___x_3122_, v_sym_3119_);
v___x_3124_ = lean_string_append(v___x_3123_, v___x_3122_);
v___x_3125_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3119_, v___x_3124_, v_a_3120_, v_a_3121_);
return v___x_3125_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3130_, uint8_t v_includeIdent_3131_){
_start:
{
lean_object* v___f_3132_; lean_object* v___f_3133_; 
v___f_3132_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3133_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3131_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_sym_3130_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3137_, 0, v___f_3132_);
lean_ctor_set(v___x_3137_, 1, v___f_3133_);
lean_ctor_set(v___x_3137_, 2, v___x_3136_);
return v___x_3137_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3138_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_sym_3130_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3141_, 0, v___f_3132_);
lean_ctor_set(v___x_3141_, 1, v___f_3133_);
lean_ctor_set(v___x_3141_, 2, v___x_3140_);
return v___x_3141_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbolInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_3130_ = stack[0].m_obj;
uint8_t v_includeIdent_3131_ = stack[1].m_num;
lean_object* v_res_3142_;
v_res_3142_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3130_, v_includeIdent_3131_);
stack->m_obj
 = v_res_3142_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3143_, lean_object* v_includeIdent_3144_){
_start:
{
uint8_t v_includeIdent_boxed_3145_; lean_object* v_res_3146_; 
v_includeIdent_boxed_3145_ = lean_unbox(v_includeIdent_3144_);
v_res_3146_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3143_, v_includeIdent_boxed_3145_);
return v_res_3146_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3147_, uint8_t v_includeIdent_3148_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_str_3153_; lean_object* v_startInclusive_3154_; lean_object* v_endExclusive_3155_; lean_object* v_sym_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = lean_string_utf8_byte_size(v_sym_3147_);
v___x_3151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3151_, 0, v_sym_3147_);
lean_ctor_set(v___x_3151_, 1, v___x_3149_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
v___x_3152_ = l_String_Slice_trimAscii(v___x_3151_);
v_str_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc_ref(v_str_3153_);
v_startInclusive_3154_ = lean_ctor_get(v___x_3152_, 1);
lean_inc(v_startInclusive_3154_);
v_endExclusive_3155_ = lean_ctor_get(v___x_3152_, 2);
lean_inc(v_endExclusive_3155_);
lean_dec_ref(v___x_3152_);
v_sym_3156_ = lean_string_utf8_extract_fast(v_str_3153_, v_startInclusive_3154_, v_endExclusive_3155_);
lean_dec(v_endExclusive_3155_);
lean_dec(v_startInclusive_3154_);
lean_dec_ref(v_str_3153_);
lean_inc_ref(v_sym_3156_);
v___x_3157_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3156_, v_includeIdent_3148_);
v___x_3158_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3158_, 0, v_sym_3156_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbolNoAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_3147_ = stack[0].m_obj;
uint8_t v_includeIdent_3148_ = stack[1].m_num;
lean_object* v_res_3160_;
v_res_3160_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3147_, v_includeIdent_3148_);
stack->m_obj
 = v_res_3160_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3161_, lean_object* v_includeIdent_3162_){
_start:
{
uint8_t v_includeIdent_boxed_3163_; lean_object* v_res_3164_; 
v_includeIdent_boxed_3163_ = lean_unbox(v_includeIdent_3162_);
v_res_3164_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3161_, v_includeIdent_boxed_3163_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3165_, lean_object* v_errorMsg_3166_, lean_object* v_j_3167_, lean_object* v_c_3168_, lean_object* v_s_3169_){
_start:
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_string_utf8_at_end(v_sym_3165_, v_j_3167_);
if (v___x_3170_ == 0)
{
lean_object* v_pos_3171_; lean_object* v_toInputContext_3172_; uint8_t v___x_3173_; 
v_pos_3171_ = lean_ctor_get(v_s_3169_, 2);
v_toInputContext_3172_ = lean_ctor_get(v_c_3168_, 0);
v___x_3173_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3172_, v_pos_3171_);
if (v___x_3173_ == 0)
{
lean_object* v_inputString_3174_; uint32_t v___x_3175_; uint32_t v___x_3176_; uint8_t v___x_3177_; 
v_inputString_3174_ = lean_ctor_get(v_toInputContext_3172_, 0);
v___x_3175_ = lean_string_utf8_get_fast(v_sym_3165_, v_j_3167_);
v___x_3176_ = lean_string_utf8_get_fast(v_inputString_3174_, v_pos_3171_);
v___x_3177_ = lean_uint32_dec_eq(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; 
lean_dec(v_j_3167_);
v___x_3178_ = l_Lean_Parser_ParserState_mkError(v_s_3169_, v_errorMsg_3166_);
return v___x_3178_;
}
else
{
if (v___x_3173_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_inc(v_pos_3171_);
v___x_3179_ = lean_string_utf8_next_fast(v_sym_3165_, v_j_3167_);
lean_dec(v_j_3167_);
v___x_3180_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3169_, v_c_3168_, v_pos_3171_);
lean_dec(v_pos_3171_);
v_j_3167_ = v___x_3179_;
v_s_3169_ = v___x_3180_;
goto _start;
}
else
{
lean_object* v___x_3182_; 
lean_dec(v_j_3167_);
v___x_3182_ = l_Lean_Parser_ParserState_mkError(v_s_3169_, v_errorMsg_3166_);
return v___x_3182_;
}
}
}
else
{
lean_object* v___x_3183_; 
lean_dec(v_j_3167_);
v___x_3183_ = l_Lean_Parser_ParserState_mkError(v_s_3169_, v_errorMsg_3166_);
return v___x_3183_;
}
}
else
{
lean_dec(v_j_3167_);
lean_dec_ref(v_errorMsg_3166_);
return v_s_3169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3184_, lean_object* v_errorMsg_3185_, lean_object* v_j_3186_, lean_object* v_c_3187_, lean_object* v_s_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3184_, v_errorMsg_3185_, v_j_3186_, v_c_3187_, v_s_3188_);
lean_dec_ref(v_c_3187_);
lean_dec_ref(v_sym_3184_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3190_, lean_object* v_errorMsg_3191_, lean_object* v_j_3192_, lean_object* v_c_3193_, lean_object* v_s_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3190_, v_errorMsg_3191_, v_j_3192_, v_c_3193_, v_s_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3196_, lean_object* v_errorMsg_3197_, lean_object* v_j_3198_, lean_object* v_c_3199_, lean_object* v_s_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_Parser_strAux(v_sym_3196_, v_errorMsg_3197_, v_j_3198_, v_c_3199_, v_s_3200_);
lean_dec_ref(v_c_3199_);
lean_dec_ref(v_sym_3196_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3202_, lean_object* v_i_3203_){
_start:
{
lean_object* v_zero_3204_; uint8_t v_isZero_3205_; 
v_zero_3204_ = lean_unsigned_to_nat(0u);
v_isZero_3205_ = lean_nat_dec_eq(v_i_3203_, v_zero_3204_);
if (v_isZero_3205_ == 1)
{
lean_object* v___x_3206_; 
lean_dec(v_i_3203_);
v___x_3206_ = lean_box(0);
return v___x_3206_;
}
else
{
lean_object* v_one_3207_; lean_object* v_n_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v_one_3207_ = lean_unsigned_to_nat(1u);
v_n_3208_ = lean_nat_sub(v_i_3203_, v_one_3207_);
lean_dec(v_i_3203_);
v___x_3209_ = l_Subarray_get___redArg(v_as_3202_, v_n_3208_);
v___x_3210_ = l_Lean_Syntax_isNone(v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; 
lean_dec(v_n_3208_);
v___x_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
return v___x_3211_;
}
else
{
lean_dec(v___x_3209_);
v_i_3203_ = v_n_3208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3213_, lean_object* v_i_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3213_, v_i_3214_);
lean_dec_ref(v_as_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3216_){
_start:
{
lean_object* v___x_3217_; lean_object* v_start_3218_; lean_object* v_stop_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3217_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3216_);
v_start_3218_ = lean_ctor_get(v___x_3217_, 1);
v_stop_3219_ = lean_ctor_get(v___x_3217_, 2);
v___x_3220_ = lean_nat_sub(v_stop_3219_, v_start_3218_);
v___x_3221_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3217_, v___x_3220_);
lean_dec_ref(v___x_3217_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_box(0);
return v___x_3222_;
}
else
{
lean_object* v_val_3223_; 
v_val_3223_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_val_3223_);
lean_dec_ref_known(v___x_3221_, 1);
return v_val_3223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3224_, lean_object* v_i_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3224_, v_i_3225_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3228_, lean_object* v_i_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3228_, v_i_3229_, v_a_3230_);
lean_dec_ref(v_as_3228_);
return v_res_3231_;
}
}
uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Syntax_getTailInfo(v_prev_3232_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_trailing_3234_; lean_object* v_startPos_3235_; lean_object* v_stopPos_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_trailing_3234_ = lean_ctor_get(v___x_3233_, 2);
lean_inc_ref(v_trailing_3234_);
lean_dec_ref_known(v___x_3233_, 4);
v_startPos_3235_ = lean_ctor_get(v_trailing_3234_, 1);
lean_inc(v_startPos_3235_);
v_stopPos_3236_ = lean_ctor_get(v_trailing_3234_, 2);
lean_inc(v_stopPos_3236_);
lean_dec_ref(v_trailing_3234_);
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_add(v_startPos_3235_, v___x_3237_);
lean_dec(v_startPos_3235_);
v___x_3239_ = lean_nat_dec_le(v___x_3238_, v_stopPos_3236_);
lean_dec(v_stopPos_3236_);
lean_dec(v___x_3238_);
return v___x_3239_;
}
else
{
uint8_t v___x_3240_; 
lean_dec(v___x_3233_);
v___x_3240_ = 0;
return v___x_3240_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_checkTailWs_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_3232_ = stack[0].m_obj;
uint8_t v_res_3241_;
v_res_3241_ = l_Lean_Parser_checkTailWs(v_prev_3232_);
stack->m_num = v_res_3241_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Lean_Parser_checkTailWs(v_prev_3242_);
lean_dec(v_prev_3242_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3245_, lean_object* v_s_3246_){
_start:
{
lean_object* v_stxStack_3247_; lean_object* v_prev_3248_; uint8_t v___x_3249_; 
v_stxStack_3247_ = lean_ctor_get(v_s_3246_, 0);
lean_inc_ref(v_stxStack_3247_);
v_prev_3248_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3247_);
v___x_3249_ = l_Lean_Parser_checkTailWs(v_prev_3248_);
lean_dec(v_prev_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_Parser_ParserState_mkError(v_s_3246_, v_errorMsg_3245_);
return v___x_3250_;
}
else
{
lean_dec_ref(v_errorMsg_3245_);
return v_s_3246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3251_, lean_object* v_x_3252_, lean_object* v_s_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3251_, v_s_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3255_, lean_object* v_x_3256_, lean_object* v_s_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3255_, v_x_3256_, v_s_3257_);
lean_dec_ref(v_x_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3259_){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3261_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3261_, 0, v_errorMsg_3259_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
return v___x_3262_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3271_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3272_ = l_Lean_addBuiltinDocString(v___x_3270_, v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3273_;
v_res_3273_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
stack->m_obj
 = v_res_3273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3276_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = l_String_instInhabitedSlice;
v___x_3278_ = lean_panic_fn_borrowed(v___x_3277_, v_msg_3276_);
return v___x_3278_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3279_, lean_object* v_a_3280_, uint8_t v_b_3281_){
_start:
{
lean_object* v_str_3282_; lean_object* v_startInclusive_3283_; lean_object* v_endExclusive_3284_; lean_object* v___x_3285_; uint8_t v_decide_3286_; 
v_str_3282_ = lean_ctor_get(v_s_3279_, 0);
v_startInclusive_3283_ = lean_ctor_get(v_s_3279_, 1);
v_endExclusive_3284_ = lean_ctor_get(v_s_3279_, 2);
v___x_3285_ = lean_nat_sub(v_endExclusive_3284_, v_startInclusive_3283_);
v_decide_3286_ = lean_nat_dec_eq(v_a_3280_, v___x_3285_);
lean_dec(v___x_3285_);
if (v_decide_3286_ == 0)
{
uint32_t v___x_3287_; lean_object* v___x_3288_; uint32_t v___x_3289_; uint8_t v___x_3290_; 
v___x_3287_ = 10;
v___x_3288_ = lean_nat_add(v_startInclusive_3283_, v_a_3280_);
lean_dec(v_a_3280_);
v___x_3289_ = lean_string_utf8_get_fast(v_str_3282_, v___x_3288_);
v___x_3290_ = lean_uint32_dec_eq(v___x_3289_, v___x_3287_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = lean_string_utf8_next_fast(v_str_3282_, v___x_3288_);
lean_dec(v___x_3288_);
v___x_3292_ = lean_nat_sub(v___x_3291_, v_startInclusive_3283_);
v_a_3280_ = v___x_3292_;
v_b_3281_ = v___x_3290_;
goto _start;
}
else
{
lean_dec(v___x_3288_);
return v___x_3290_;
}
}
else
{
lean_dec(v_a_3280_);
return v_b_3281_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3279_ = stack[0].m_obj;
lean_object* v_a_3280_ = stack[1].m_obj;
uint8_t v_b_3281_ = stack[2].m_num;
uint8_t v_res_3294_;
v_res_3294_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3279_, v_a_3280_, v_b_3281_);
stack->m_num = v_res_3294_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3295_, lean_object* v_a_3296_, lean_object* v_b_3297_){
_start:
{
uint8_t v_b_boxed_3298_; uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_b_boxed_3298_ = lean_unbox(v_b_3297_);
v_res_3299_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3295_, v_a_3296_, v_b_boxed_3298_);
lean_dec_ref(v_s_3295_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3301_){
_start:
{
lean_object* v_searcher_3302_; uint8_t v___x_3303_; uint8_t v___x_3304_; 
v_searcher_3302_ = lean_unsigned_to_nat(0u);
v___x_3303_ = 0;
v___x_3304_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3301_, v_searcher_3302_, v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3301_ = stack[0].m_obj;
uint8_t v_res_3305_;
v_res_3305_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3301_);
stack->m_num = v_res_3305_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3306_);
lean_dec_ref(v_s_3306_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3312_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3313_ = lean_unsigned_to_nat(14u);
v___x_3314_ = lean_unsigned_to_nat(22u);
v___x_3315_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3316_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3317_ = l_mkPanicMessageWithDecl(v___x_3316_, v___x_3315_, v___x_3314_, v___x_3313_, v___x_3312_);
return v___x_3317_;
}
}
uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Syntax_getTailInfo(v_prev_3318_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_trailing_3320_; lean_object* v_str_3321_; lean_object* v_startPos_3322_; lean_object* v_stopPos_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3339_; 
v_trailing_3320_ = lean_ctor_get(v___x_3319_, 2);
lean_inc_ref(v_trailing_3320_);
lean_dec_ref_known(v___x_3319_, 4);
v_str_3321_ = lean_ctor_get(v_trailing_3320_, 0);
v_startPos_3322_ = lean_ctor_get(v_trailing_3320_, 1);
v_stopPos_3323_ = lean_ctor_get(v_trailing_3320_, 2);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_trailing_3320_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3325_ = v_trailing_3320_;
v_isShared_3326_ = v_isSharedCheck_3339_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_stopPos_3323_);
lean_inc(v_startPos_3322_);
lean_inc(v_str_3321_);
lean_dec(v_trailing_3320_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3339_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
uint8_t v___y_3328_; uint8_t v___x_3336_; 
v___x_3336_ = lean_string_is_valid_pos(v_str_3321_, v_startPos_3322_);
if (v___x_3336_ == 0)
{
v___y_3328_ = v___x_3336_;
goto v___jp_3327_;
}
else
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_string_is_valid_pos(v_str_3321_, v_stopPos_3323_);
if (v___x_3337_ == 0)
{
v___y_3328_ = v___x_3337_;
goto v___jp_3327_;
}
else
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_nat_dec_le(v_startPos_3322_, v_stopPos_3323_);
v___y_3328_ = v___x_3338_;
goto v___jp_3327_;
}
}
v___jp_3327_:
{
if (v___y_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
lean_del_object(v___x_3325_);
lean_dec(v_stopPos_3323_);
lean_dec(v_startPos_3322_);
lean_dec_ref(v_str_3321_);
v___x_3329_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3330_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3329_);
v___x_3331_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3330_);
lean_dec_ref(v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v___x_3333_; 
if (v_isShared_3326_ == 0)
{
v___x_3333_ = v___x_3325_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_str_3321_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_startPos_3322_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_stopPos_3323_);
v___x_3333_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
uint8_t v___x_3334_; 
v___x_3334_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3333_);
lean_dec_ref(v___x_3333_);
return v___x_3334_;
}
}
}
}
}
else
{
uint8_t v___x_3340_; 
lean_dec(v___x_3319_);
v___x_3340_ = 0;
return v___x_3340_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_checkTailLinebreak_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_3318_ = stack[0].m_obj;
uint8_t v_res_3341_;
v_res_3341_ = l_Lean_Parser_checkTailLinebreak(v_prev_3318_);
stack->m_num = v_res_3341_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3342_){
_start:
{
uint8_t v_res_3343_; lean_object* v_r_3344_; 
v_res_3343_ = l_Lean_Parser_checkTailLinebreak(v_prev_3342_);
lean_dec(v_prev_3342_);
v_r_3344_ = lean_box(v_res_3343_);
return v_r_3344_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3345_, lean_object* v_inst_3346_, lean_object* v_R_3347_, lean_object* v_a_3348_, uint8_t v_b_3349_, lean_object* v_c_3350_){
_start:
{
uint8_t v___x_3351_; 
v___x_3351_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3345_, v_a_3348_, v_b_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3345_ = stack[0].m_obj;
lean_object* v_a_3348_ = stack[3].m_obj;
uint8_t v_b_3349_ = stack[4].m_num;
uint8_t v_res_3352_;
v_res_3352_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3345_, lean_box(0), lean_box(0), v_a_3348_, v_b_3349_, lean_box(0));
stack->m_num = v_res_3352_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3353_, lean_object* v_inst_3354_, lean_object* v_R_3355_, lean_object* v_a_3356_, lean_object* v_b_3357_, lean_object* v_c_3358_){
_start:
{
uint8_t v_b_boxed_3359_; uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_b_boxed_3359_ = lean_unbox(v_b_3357_);
v_res_3360_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3353_, v_inst_3354_, v_R_3355_, v_a_3356_, v_b_boxed_3359_, v_c_3358_);
lean_dec_ref(v_s_3353_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3362_, lean_object* v_s_3363_){
_start:
{
lean_object* v_stxStack_3364_; lean_object* v_prev_3365_; uint8_t v___x_3366_; 
v_stxStack_3364_ = lean_ctor_get(v_s_3363_, 0);
v_prev_3365_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3364_);
v___x_3366_ = l_Lean_Parser_checkTailLinebreak(v_prev_3365_);
lean_dec(v_prev_3365_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Parser_ParserState_mkError(v_s_3363_, v_errorMsg_3362_);
return v___x_3367_;
}
else
{
lean_dec_ref(v_errorMsg_3362_);
return v_s_3363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3368_, lean_object* v_x_3369_, lean_object* v_s_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3368_, v_s_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3372_, lean_object* v_x_3373_, lean_object* v_s_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3372_, v_x_3373_, v_s_3374_);
lean_dec_ref(v_x_3373_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3376_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3378_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3378_, 0, v_errorMsg_3376_);
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
return v___x_3379_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3388_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3389_ = l_Lean_addBuiltinDocString(v___x_3387_, v___x_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3390_;
v_res_3390_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
stack->m_obj
 = v_res_3390_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3392_;
}
}
uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3393_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_Syntax_getTailInfo(v_prev_3393_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_trailing_3395_; lean_object* v_startPos_3396_; lean_object* v_stopPos_3397_; uint8_t v_decide_3398_; 
v_trailing_3395_ = lean_ctor_get(v___x_3394_, 2);
lean_inc_ref(v_trailing_3395_);
lean_dec_ref_known(v___x_3394_, 4);
v_startPos_3396_ = lean_ctor_get(v_trailing_3395_, 1);
lean_inc(v_startPos_3396_);
v_stopPos_3397_ = lean_ctor_get(v_trailing_3395_, 2);
lean_inc(v_stopPos_3397_);
lean_dec_ref(v_trailing_3395_);
v_decide_3398_ = lean_nat_dec_eq(v_stopPos_3397_, v_startPos_3396_);
lean_dec(v_startPos_3396_);
lean_dec(v_stopPos_3397_);
return v_decide_3398_;
}
else
{
uint8_t v___x_3399_; 
lean_dec(v___x_3394_);
v___x_3399_ = 0;
return v___x_3399_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_checkTailNoWs_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_3393_ = stack[0].m_obj;
uint8_t v_res_3400_;
v_res_3400_ = l_Lean_Parser_checkTailNoWs(v_prev_3393_);
stack->m_num = v_res_3400_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_Lean_Parser_checkTailNoWs(v_prev_3401_);
lean_dec(v_prev_3401_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3404_, lean_object* v_s_3405_){
_start:
{
lean_object* v_stxStack_3406_; lean_object* v_prev_3407_; uint8_t v___x_3408_; 
v_stxStack_3406_ = lean_ctor_get(v_s_3405_, 0);
lean_inc_ref(v_stxStack_3406_);
v_prev_3407_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3406_);
v___x_3408_ = l_Lean_Parser_checkTailNoWs(v_prev_3407_);
lean_dec(v_prev_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Parser_ParserState_mkError(v_s_3405_, v_errorMsg_3404_);
return v___x_3409_;
}
else
{
lean_dec_ref(v_errorMsg_3404_);
return v_s_3405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3410_, lean_object* v_x_3411_, lean_object* v_s_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3410_, v_s_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3414_, lean_object* v_x_3415_, lean_object* v_s_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3414_, v_x_3415_, v_s_3416_);
lean_dec_ref(v_x_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3418_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3419_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3420_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3420_, 0, v_errorMsg_3418_);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
return v___x_3421_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3430_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3431_ = l_Lean_addBuiltinDocString(v___x_3429_, v___x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3432_;
v_res_3432_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
stack->m_obj
 = v_res_3432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3434_;
}
}
uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3435_, lean_object* v_asciiSym_3436_, lean_object* v_s_3437_){
_start:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_string_dec_eq(v_s_3437_, v_sym_3435_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_string_dec_eq(v_s_3437_, v_asciiSym_3436_);
return v___x_3439_;
}
else
{
return v___x_3438_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_unicodeSymbolFnAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_3435_ = stack[0].m_obj;
lean_object* v_asciiSym_3436_ = stack[1].m_obj;
lean_object* v_s_3437_ = stack[2].m_obj;
uint8_t v_res_3440_;
v_res_3440_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3435_, v_asciiSym_3436_, v_s_3437_);
stack->m_num = v_res_3440_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3441_, lean_object* v_asciiSym_3442_, lean_object* v_s_3443_){
_start:
{
uint8_t v_res_3444_; lean_object* v_r_3445_; 
v_res_3444_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3441_, v_asciiSym_3442_, v_s_3443_);
lean_dec_ref(v_s_3443_);
lean_dec_ref(v_asciiSym_3442_);
lean_dec_ref(v_sym_3441_);
v_r_3445_ = lean_box(v_res_3444_);
return v_r_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3446_, lean_object* v_asciiSym_3447_, lean_object* v_expected_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v___f_3451_; lean_object* v___x_3452_; 
v___f_3451_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3451_, 0, v_sym_3446_);
lean_closure_set(v___f_3451_, 1, v_asciiSym_3447_);
v___x_3452_ = l_Lean_Parser_satisfySymbolFn(v___f_3451_, v_expected_3448_, v_a_3449_, v_a_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3453_, lean_object* v_sym_3454_, lean_object* v_tks_3455_){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_asciiSym_3453_);
lean_ctor_set(v___x_3456_, 1, v_tks_3455_);
v___x_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_sym_3454_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3458_, lean_object* v_asciiSym_3459_){
_start:
{
lean_object* v___f_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_inc_ref(v_sym_3458_);
lean_inc_ref(v_asciiSym_3459_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3460_, 0, v_asciiSym_3459_);
lean_closure_set(v___f_3460_, 1, v_sym_3458_);
v___f_3461_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3463_, 0, v_asciiSym_3459_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3464_, 0, v_sym_3458_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
v___x_3466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3466_, 0, v___f_3460_);
lean_ctor_set(v___x_3466_, 1, v___f_3461_);
lean_ctor_set(v___x_3466_, 2, v___x_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3468_, lean_object* v_asciiSym_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3472_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3473_ = lean_string_append(v___x_3472_, v_sym_3468_);
v___x_3474_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3475_ = lean_string_append(v___x_3473_, v___x_3474_);
v___x_3476_ = lean_string_append(v___x_3475_, v_asciiSym_3469_);
v___x_3477_ = lean_string_append(v___x_3476_, v___x_3472_);
v___x_3478_ = lean_box(0);
v___x_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3468_, v_asciiSym_3469_, v___x_3479_, v_a_3470_, v_a_3471_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3481_, lean_object* v_asciiSym_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v_str_3487_; lean_object* v_startInclusive_3488_; lean_object* v_endExclusive_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3506_; 
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_string_utf8_byte_size(v_sym_3481_);
v___x_3485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3485_, 0, v_sym_3481_);
lean_ctor_set(v___x_3485_, 1, v___x_3483_);
lean_ctor_set(v___x_3485_, 2, v___x_3484_);
v___x_3486_ = l_String_Slice_trimAscii(v___x_3485_);
v_str_3487_ = lean_ctor_get(v___x_3486_, 0);
v_startInclusive_3488_ = lean_ctor_get(v___x_3486_, 1);
v_endExclusive_3489_ = lean_ctor_get(v___x_3486_, 2);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3491_ = v___x_3486_;
v_isShared_3492_ = v_isSharedCheck_3506_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_endExclusive_3489_);
lean_inc(v_startInclusive_3488_);
lean_inc(v_str_3487_);
lean_dec(v___x_3486_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3506_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3493_ = lean_string_utf8_byte_size(v_asciiSym_3482_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 2, v___x_3493_);
lean_ctor_set(v___x_3491_, 1, v___x_3483_);
lean_ctor_set(v___x_3491_, 0, v_asciiSym_3482_);
v___x_3495_ = v___x_3491_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_asciiSym_3482_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3496_; lean_object* v_str_3497_; lean_object* v_startInclusive_3498_; lean_object* v_endExclusive_3499_; lean_object* v_sym_3500_; lean_object* v_asciiSym_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3496_ = l_String_Slice_trimAscii(v___x_3495_);
v_str_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc_ref(v_str_3497_);
v_startInclusive_3498_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_startInclusive_3498_);
v_endExclusive_3499_ = lean_ctor_get(v___x_3496_, 2);
lean_inc(v_endExclusive_3499_);
lean_dec_ref(v___x_3496_);
v_sym_3500_ = lean_string_utf8_extract_fast(v_str_3487_, v_startInclusive_3488_, v_endExclusive_3489_);
lean_dec(v_endExclusive_3489_);
lean_dec(v_startInclusive_3488_);
lean_dec_ref(v_str_3487_);
v_asciiSym_3501_ = lean_string_utf8_extract_fast(v_str_3497_, v_startInclusive_3498_, v_endExclusive_3499_);
lean_dec(v_endExclusive_3499_);
lean_dec(v_startInclusive_3498_);
lean_dec_ref(v_str_3497_);
lean_inc_ref(v_asciiSym_3501_);
lean_inc_ref(v_sym_3500_);
v___x_3502_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3500_, v_asciiSym_3501_);
v___x_3503_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3503_, 0, v_sym_3500_);
lean_closure_set(v___x_3503_, 1, v_asciiSym_3501_);
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
return v___x_3504_;
}
}
}
}
lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3507_, lean_object* v_asciiSym_3508_, uint8_t v_preserveForPP_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3507_, v_asciiSym_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT void l_Lean_Parser_unicodeSymbolNoAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_3507_ = stack[0].m_obj;
lean_object* v_asciiSym_3508_ = stack[1].m_obj;
uint8_t v_preserveForPP_3509_ = stack[2].m_num;
lean_object* v_res_3511_;
v_res_3511_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3507_, v_asciiSym_3508_, v_preserveForPP_3509_);
stack->m_obj
 = v_res_3511_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3512_, lean_object* v_asciiSym_3513_, lean_object* v_preserveForPP_3514_){
_start:
{
uint8_t v_preserveForPP_boxed_3515_; lean_object* v_res_3516_; 
v_preserveForPP_boxed_3515_ = lean_unbox(v_preserveForPP_3514_);
v_res_3516_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3512_, v_asciiSym_3513_, v_preserveForPP_boxed_3515_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3517_){
_start:
{
lean_object* v___f_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___f_3518_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3519_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3520_ = lean_box(0);
v___x_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_k_3517_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3523_, 0, v___f_3518_);
lean_ctor_set(v___x_3523_, 1, v___f_3519_);
lean_ctor_set(v___x_3523_, 2, v___x_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3524_, lean_object* v_desc_3525_, lean_object* v_c_3526_, lean_object* v_s_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_s_3530_; lean_object* v_stxStack_3531_; lean_object* v_errorMsg_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3528_ = lean_box(0);
lean_inc_ref(v_desc_3525_);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_desc_3525_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v_s_3530_ = l_Lean_Parser_tokenFn(v___x_3529_, v_c_3526_, v_s_3527_);
v_stxStack_3531_ = lean_ctor_get(v_s_3530_, 0);
v_errorMsg_3532_ = lean_ctor_get(v_s_3530_, 4);
v___x_3533_ = lean_box(0);
v___x_3534_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_dec_ref(v_desc_3525_);
return v_s_3530_;
}
else
{
lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3531_);
v___x_3536_ = l_Lean_Syntax_isOfKind(v___x_3535_, v_k_3524_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3530_, v_desc_3525_, v___x_3537_);
return v___x_3538_;
}
else
{
lean_dec_ref(v_desc_3525_);
return v_s_3530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3539_, lean_object* v_desc_3540_, lean_object* v_c_3541_, lean_object* v_s_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Parser_expectTokenFn(v_k_3539_, v_desc_3540_, v_c_3541_, v_s_3542_);
lean_dec(v_k_3539_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3547_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3548_ = l_Lean_Parser_expectTokenFn(v___x_3546_, v___x_3547_, v_a_3544_, v_a_3545_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3550_ = l_Lean_Parser_mkAtomicInfo(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3552_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
lean_ctor_set(v___x_3553_, 1, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3558_, lean_object* v_s_3559_){
_start:
{
lean_object* v_pos_3560_; uint8_t v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_pos_3560_ = lean_ctor_get(v_s_3559_, 2);
lean_inc(v_pos_3560_);
v___x_3561_ = 1;
v___x_3562_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3563_ = l_Lean_Parser_hexNumberFn(v_pos_3560_, v___x_3561_, v___x_3562_, v_ctx_3558_, v_s_3559_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3565_ = l_Lean_Parser_mkAtomicInfo(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3567_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3574_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3575_ = l_Lean_Parser_expectTokenFn(v___x_3573_, v___x_3574_, v_a_3571_, v_a_3572_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3577_ = l_Lean_Parser_mkAtomicInfo(v___x_3576_);
return v___x_3577_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3579_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___x_3578_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3586_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3587_ = l_Lean_Parser_expectTokenFn(v___x_3585_, v___x_3586_, v_a_3583_, v_a_3584_);
return v___x_3587_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3589_ = l_Lean_Parser_mkAtomicInfo(v___x_3588_);
return v___x_3589_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3591_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v___x_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3598_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3599_ = l_Lean_Parser_expectTokenFn(v___x_3597_, v___x_3598_, v_a_3595_, v_a_3596_);
return v___x_3599_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3601_ = l_Lean_Parser_mkAtomicInfo(v___x_3600_);
return v___x_3601_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3603_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v___x_3602_);
return v___x_3604_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3613_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3614_ = l_Lean_Parser_expectTokenFn(v___x_3612_, v___x_3613_, v_a_3610_, v_a_3611_);
return v___x_3614_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3616_ = l_Lean_Parser_mkAtomicInfo(v___x_3615_);
return v___x_3616_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3618_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
lean_ctor_set(v___x_3619_, 1, v___x_3617_);
return v___x_3619_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_c_3624_, lean_object* v_s_3625_){
_start:
{
lean_object* v_toCacheableParserContext_3626_; lean_object* v_forbiddenTks_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v_toCacheableParserContext_3626_ = lean_ctor_get(v_c_3624_, 2);
v_forbiddenTks_3627_ = lean_ctor_get(v_toCacheableParserContext_3626_, 3);
v___x_3628_ = lean_array_get_size(v_forbiddenTks_3627_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_nat_dec_eq(v___x_3628_, v___x_3629_);
if (v___x_3630_ == 0)
{
lean_object* v_pos_3631_; lean_object* v_iniSz_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v_s_3635_; lean_object* v_stxStack_3636_; lean_object* v_errorMsg_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
lean_inc_ref(v_forbiddenTks_3627_);
v_pos_3631_ = lean_ctor_get(v_s_3625_, 2);
lean_inc(v_pos_3631_);
v_iniSz_3632_ = l_Lean_Parser_ParserState_stackSize(v_s_3625_);
v___x_3633_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3634_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v_s_3635_ = l_Lean_Parser_expectTokenFn(v___x_3633_, v___x_3634_, v_c_3624_, v_s_3625_);
v_stxStack_3636_ = lean_ctor_get(v_s_3635_, 0);
v_errorMsg_3637_ = lean_ctor_get(v_s_3635_, 4);
v___x_3638_ = lean_box(0);
v___x_3639_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_dec(v_iniSz_3632_);
lean_dec(v_pos_3631_);
lean_dec_ref(v_forbiddenTks_3627_);
return v_s_3635_;
}
else
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3636_);
if (lean_obj_tag(v___x_3640_) == 3)
{
lean_object* v_rawVal_3641_; lean_object* v_str_3642_; lean_object* v_startPos_3643_; lean_object* v_stopPos_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v_rawVal_3641_ = lean_ctor_get(v___x_3640_, 1);
lean_inc_ref(v_rawVal_3641_);
lean_dec_ref_known(v___x_3640_, 4);
v_str_3642_ = lean_ctor_get(v_rawVal_3641_, 0);
lean_inc_ref(v_str_3642_);
v_startPos_3643_ = lean_ctor_get(v_rawVal_3641_, 1);
lean_inc(v_startPos_3643_);
v_stopPos_3644_ = lean_ctor_get(v_rawVal_3641_, 2);
lean_inc(v_stopPos_3644_);
lean_dec_ref(v_rawVal_3641_);
v___x_3645_ = lean_string_utf8_extract(v_str_3642_, v_startPos_3643_, v_stopPos_3644_);
lean_dec(v_stopPos_3644_);
lean_dec(v_startPos_3643_);
lean_dec_ref(v_str_3642_);
v___x_3646_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_3627_, v___x_3645_);
lean_dec_ref(v___x_3645_);
lean_dec_ref(v_forbiddenTks_3627_);
if (v___x_3646_ == 0)
{
lean_dec(v_iniSz_3632_);
lean_dec(v_pos_3631_);
return v_s_3635_;
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_iniSz_3632_);
v___x_3649_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_3635_, v___x_3647_, v_pos_3631_, v___x_3648_);
lean_dec_ref_known(v___x_3648_, 1);
return v___x_3649_;
}
}
else
{
lean_dec(v___x_3640_);
lean_dec(v_iniSz_3632_);
lean_dec(v_pos_3631_);
lean_dec_ref(v_forbiddenTks_3627_);
return v_s_3635_;
}
}
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3650_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3651_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3652_ = l_Lean_Parser_expectTokenFn(v___x_3650_, v___x_3651_, v_c_3624_, v_s_3625_);
return v___x_3652_;
}
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__0));
v___x_3654_ = l_Lean_Parser_mkAtomicInfo(v___x_3653_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
v___x_3656_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot(void){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__1, &l_Lean_Parser_identNoAntiquot___closed__1_once, _init_l_Lean_Parser_identNoAntiquot___closed__1);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* v_id_3670_, lean_object* v_c_3671_, lean_object* v_s_3672_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v_s_3675_; lean_object* v_stxStack_3676_; lean_object* v_errorMsg_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3673_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3674_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__0));
v_s_3675_ = l_Lean_Parser_tokenFn(v___x_3674_, v_c_3671_, v_s_3672_);
v_stxStack_3676_ = lean_ctor_get(v_s_3675_, 0);
v_errorMsg_3677_ = lean_ctor_get(v_s_3675_, 4);
v___x_3678_ = lean_box(0);
v___x_3679_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_dec(v_id_3670_);
return v_s_3675_;
}
else
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3676_);
if (lean_obj_tag(v___x_3680_) == 3)
{
lean_object* v_val_3681_; uint8_t v___x_3682_; 
v_val_3681_ = lean_ctor_get(v___x_3680_, 2);
lean_inc(v_val_3681_);
lean_dec_ref_known(v___x_3680_, 4);
v___x_3682_ = lean_name_eq(v_val_3681_, v_id_3670_);
lean_dec(v_val_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3683_ = ((lean_object*)(l_Lean_Parser_identEqFn___closed__1));
v___x_3684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3670_, v___x_3679_);
v___x_3685_ = lean_string_append(v___x_3683_, v___x_3684_);
lean_dec_ref(v___x_3684_);
v___x_3686_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3687_ = lean_string_append(v___x_3685_, v___x_3686_);
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3675_, v___x_3687_, v___x_3688_);
return v___x_3689_;
}
else
{
lean_dec(v_id_3670_);
return v_s_3675_;
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_dec(v___x_3680_);
lean_dec(v_id_3670_);
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3675_, v___x_3673_, v___x_3690_);
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* v_id_3692_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = lean_obj_once(&l_Lean_Parser_identNoAntiquot___closed__0, &l_Lean_Parser_identNoAntiquot___closed__0_once, _init_l_Lean_Parser_identNoAntiquot___closed__0);
v___x_3694_ = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(v___x_3694_, 0, v_id_3692_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* v_c_3699_, lean_object* v_s_3700_){
_start:
{
lean_object* v_pos_3702_; lean_object* v_str_3703_; lean_object* v_trailing_3704_; lean_object* v_s_3705_; lean_object* v_stxStack_3717_; lean_object* v_pos_3718_; uint8_t v___x_3721_; 
v_stxStack_3717_ = lean_ctor_get(v_s_3700_, 0);
v_pos_3718_ = lean_ctor_get(v_s_3700_, 2);
v___x_3721_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_3717_);
if (v___x_3721_ == 0)
{
lean_object* v_prev_3722_; lean_object* v___x_3723_; 
v_prev_3722_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3717_);
v___x_3723_ = l_Lean_Syntax_getTailInfo(v_prev_3722_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_leading_3724_; lean_object* v_pos_3725_; lean_object* v_trailing_3726_; lean_object* v_endPos_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3738_; 
v_leading_3724_ = lean_ctor_get(v___x_3723_, 0);
v_pos_3725_ = lean_ctor_get(v___x_3723_, 1);
v_trailing_3726_ = lean_ctor_get(v___x_3723_, 2);
v_endPos_3727_ = lean_ctor_get(v___x_3723_, 3);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3729_ = v___x_3723_;
v_isShared_3730_ = v_isSharedCheck_3738_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_endPos_3727_);
lean_inc(v_trailing_3726_);
lean_inc(v_pos_3725_);
lean_inc(v_leading_3724_);
lean_dec(v___x_3723_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3738_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v_str_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
lean_inc_n(v_endPos_3727_, 2);
v_str_3731_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3699_, v_endPos_3727_);
v___x_3732_ = l_Lean_Parser_ParserState_popSyntax(v_s_3700_);
lean_inc_ref(v_str_3731_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 2, v_str_3731_);
v___x_3734_ = v___x_3729_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_leading_3724_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_pos_3725_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_str_3731_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_endPos_3727_);
v___x_3734_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; lean_object* v_s_3736_; 
v___x_3735_ = l_Lean_Syntax_setTailInfo(v_prev_3722_, v___x_3734_);
v_s_3736_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3732_, v___x_3735_);
v_pos_3702_ = v_endPos_3727_;
v_str_3703_ = v_str_3731_;
v_trailing_3704_ = v_trailing_3726_;
v_s_3705_ = v_s_3736_;
goto v___jp_3701_;
}
}
}
else
{
lean_inc(v_pos_3718_);
lean_dec(v___x_3723_);
lean_dec(v_prev_3722_);
goto v___jp_3719_;
}
}
else
{
lean_inc(v_pos_3718_);
goto v___jp_3719_;
}
v___jp_3701_:
{
lean_object* v_info_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v_ident_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_inc(v_pos_3702_);
lean_inc_ref(v_str_3703_);
v_info_3706_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_3706_, 0, v_str_3703_);
lean_ctor_set(v_info_3706_, 1, v_pos_3702_);
lean_ctor_set(v_info_3706_, 2, v_trailing_3704_);
lean_ctor_set(v_info_3706_, 3, v_pos_3702_);
v___x_3707_ = lean_box(0);
v___x_3708_ = lean_box(0);
v_ident_3709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_ident_3709_, 0, v_info_3706_);
lean_ctor_set(v_ident_3709_, 1, v_str_3703_);
lean_ctor_set(v_ident_3709_, 2, v___x_3707_);
lean_ctor_set(v_ident_3709_, 3, v___x_3708_);
v___x_3710_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3711_ = lean_unsigned_to_nat(1u);
v___x_3712_ = lean_mk_empty_array_with_capacity(v___x_3711_);
v___x_3713_ = lean_array_push(v___x_3712_, v_ident_3709_);
v___x_3714_ = lean_box(2);
v___x_3715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___x_3710_);
lean_ctor_set(v___x_3715_, 2, v___x_3713_);
v___x_3716_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3705_, v___x_3715_);
return v___x_3716_;
}
v___jp_3719_:
{
lean_object* v_str_3720_; 
lean_inc(v_pos_3718_);
v_str_3720_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3699_, v_pos_3718_);
lean_inc_ref(v_str_3720_);
v_pos_3702_ = v_pos_3718_;
v_str_3703_ = v_str_3720_;
v_trailing_3704_ = v_str_3720_;
v_s_3705_ = v_s_3700_;
goto v___jp_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* v_c_3739_, lean_object* v_s_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_Parser_hygieneInfoFn(v_c_3739_, v_s_3740_);
lean_dec_ref(v_c_3739_);
return v_res_3741_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3743_ = ((lean_object*)(l_Lean_Parser_hygieneInfoFn___closed__1));
v___x_3744_ = l_Lean_Parser_nodeInfo(v___x_3743_, v___x_3742_);
return v___x_3744_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3745_ = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
v___x_3746_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__0, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__0_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__0);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v___x_3745_);
return v___x_3747_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot(void){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_obj_once(&l_Lean_Parser_hygieneInfoNoAntiquot___closed__1, &l_Lean_Parser_hygieneInfoNoAntiquot___closed__1_once, _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* v_s_3749_, lean_object* v_startStackSize_3750_){
_start:
{
lean_object* v_node_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v_node_3751_ = l_Lean_Parser_SyntaxStack_back(v_s_3749_);
v___x_3752_ = l_Lean_Parser_SyntaxStack_shrink(v_s_3749_, v_startStackSize_3750_);
v___x_3753_ = l_Lean_Parser_SyntaxStack_push(v___x_3752_, v_node_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* v_s_3754_, lean_object* v_startStackSize_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Lean_Parser_ParserState_keepTop(v_s_3754_, v_startStackSize_3755_);
lean_dec(v_startStackSize_3755_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* v_s_3757_, lean_object* v_oldStackSize_3758_){
_start:
{
lean_object* v_stxStack_3759_; lean_object* v_lhsPrec_3760_; lean_object* v_pos_3761_; lean_object* v_cache_3762_; lean_object* v_errorMsg_3763_; lean_object* v_recoveredErrors_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3772_; 
v_stxStack_3759_ = lean_ctor_get(v_s_3757_, 0);
v_lhsPrec_3760_ = lean_ctor_get(v_s_3757_, 1);
v_pos_3761_ = lean_ctor_get(v_s_3757_, 2);
v_cache_3762_ = lean_ctor_get(v_s_3757_, 3);
v_errorMsg_3763_ = lean_ctor_get(v_s_3757_, 4);
v_recoveredErrors_3764_ = lean_ctor_get(v_s_3757_, 5);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_s_3757_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3766_ = v_s_3757_;
v_isShared_3767_ = v_isSharedCheck_3772_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_recoveredErrors_3764_);
lean_inc(v_errorMsg_3763_);
lean_inc(v_cache_3762_);
lean_inc(v_pos_3761_);
lean_inc(v_lhsPrec_3760_);
lean_inc(v_stxStack_3759_);
lean_dec(v_s_3757_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3772_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3768_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3759_, v_oldStackSize_3758_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v___x_3768_);
v___x_3770_ = v___x_3766_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_lhsPrec_3760_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_pos_3761_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_cache_3762_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_errorMsg_3763_);
lean_ctor_set(v_reuseFailAlloc_3771_, 5, v_recoveredErrors_3764_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* v_s_3773_, lean_object* v_oldStackSize_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Parser_ParserState_keepNewError(v_s_3773_, v_oldStackSize_3774_);
lean_dec(v_oldStackSize_3774_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* v_s_3776_, lean_object* v_oldStackSize_3777_, lean_object* v_oldStopPos_3778_, lean_object* v_oldError_3779_, lean_object* v_oldLhsPrec_3780_){
_start:
{
lean_object* v_stxStack_3781_; lean_object* v_cache_3782_; lean_object* v_recoveredErrors_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3791_; 
v_stxStack_3781_ = lean_ctor_get(v_s_3776_, 0);
v_cache_3782_ = lean_ctor_get(v_s_3776_, 3);
v_recoveredErrors_3783_ = lean_ctor_get(v_s_3776_, 5);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_s_3776_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; lean_object* v_unused_3794_; 
v_unused_3792_ = lean_ctor_get(v_s_3776_, 4);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_s_3776_, 2);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_s_3776_, 1);
lean_dec(v_unused_3794_);
v___x_3785_ = v_s_3776_;
v_isShared_3786_ = v_isSharedCheck_3791_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_recoveredErrors_3783_);
lean_inc(v_cache_3782_);
lean_inc(v_stxStack_3781_);
lean_dec(v_s_3776_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3791_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3781_, v_oldStackSize_3777_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 4, v_oldError_3779_);
lean_ctor_set(v___x_3785_, 2, v_oldStopPos_3778_);
lean_ctor_set(v___x_3785_, 1, v_oldLhsPrec_3780_);
lean_ctor_set(v___x_3785_, 0, v___x_3787_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_oldLhsPrec_3780_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_oldStopPos_3778_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_cache_3782_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_oldError_3779_);
lean_ctor_set(v_reuseFailAlloc_3790_, 5, v_recoveredErrors_3783_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* v_s_3795_, lean_object* v_oldStackSize_3796_, lean_object* v_oldStopPos_3797_, lean_object* v_oldError_3798_, lean_object* v_oldLhsPrec_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3795_, v_oldStackSize_3796_, v_oldStopPos_3797_, v_oldError_3798_, v_oldLhsPrec_3799_);
lean_dec(v_oldStackSize_3796_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* v_s_3801_, lean_object* v_oldStackSize_3802_, lean_object* v_oldError_3803_){
_start:
{
lean_object* v_stxStack_3804_; lean_object* v_lhsPrec_3805_; lean_object* v_pos_3806_; lean_object* v_cache_3807_; lean_object* v_errorMsg_3808_; lean_object* v_recoveredErrors_3809_; lean_object* v___y_3811_; 
v_stxStack_3804_ = lean_ctor_get(v_s_3801_, 0);
v_lhsPrec_3805_ = lean_ctor_get(v_s_3801_, 1);
v_pos_3806_ = lean_ctor_get(v_s_3801_, 2);
v_cache_3807_ = lean_ctor_get(v_s_3801_, 3);
v_errorMsg_3808_ = lean_ctor_get(v_s_3801_, 4);
v_recoveredErrors_3809_ = lean_ctor_get(v_s_3801_, 5);
if (lean_obj_tag(v_errorMsg_3808_) == 1)
{
lean_object* v_val_3815_; uint8_t v___x_3816_; 
lean_inc_ref(v_errorMsg_3808_);
lean_inc_ref(v_recoveredErrors_3809_);
lean_inc_ref(v_cache_3807_);
lean_inc(v_pos_3806_);
lean_inc(v_lhsPrec_3805_);
lean_inc_ref(v_stxStack_3804_);
lean_dec_ref(v_s_3801_);
v_val_3815_ = lean_ctor_get(v_errorMsg_3808_, 0);
lean_inc(v_val_3815_);
lean_dec_ref_known(v_errorMsg_3808_, 1);
v___x_3816_ = l_Lean_Parser_instBEqError_beq(v_oldError_3803_, v_val_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Parser_Error_merge(v_oldError_3803_, v_val_3815_);
v___y_3811_ = v___x_3817_;
goto v___jp_3810_;
}
else
{
lean_dec_ref(v_oldError_3803_);
v___y_3811_ = v_val_3815_;
goto v___jp_3810_;
}
}
else
{
lean_dec_ref(v_oldError_3803_);
return v_s_3801_;
}
v___jp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3812_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3804_, v_oldStackSize_3802_);
v___x_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___y_3811_);
v___x_3814_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v_lhsPrec_3805_);
lean_ctor_set(v___x_3814_, 2, v_pos_3806_);
lean_ctor_set(v___x_3814_, 3, v_cache_3807_);
lean_ctor_set(v___x_3814_, 4, v___x_3813_);
lean_ctor_set(v___x_3814_, 5, v_recoveredErrors_3809_);
return v___x_3814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* v_s_3818_, lean_object* v_oldStackSize_3819_, lean_object* v_oldError_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3818_, v_oldStackSize_3819_, v_oldError_3820_);
lean_dec(v_oldStackSize_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* v_s_3822_, lean_object* v_startStackSize_3823_){
_start:
{
lean_object* v_stxStack_3824_; lean_object* v_lhsPrec_3825_; lean_object* v_pos_3826_; lean_object* v_cache_3827_; lean_object* v_recoveredErrors_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3837_; 
v_stxStack_3824_ = lean_ctor_get(v_s_3822_, 0);
v_lhsPrec_3825_ = lean_ctor_get(v_s_3822_, 1);
v_pos_3826_ = lean_ctor_get(v_s_3822_, 2);
v_cache_3827_ = lean_ctor_get(v_s_3822_, 3);
v_recoveredErrors_3828_ = lean_ctor_get(v_s_3822_, 5);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_s_3822_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_s_3822_, 4);
lean_dec(v_unused_3838_);
v___x_3830_ = v_s_3822_;
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_recoveredErrors_3828_);
lean_inc(v_cache_3827_);
lean_inc(v_pos_3826_);
lean_inc(v_lhsPrec_3825_);
lean_inc(v_stxStack_3824_);
lean_dec(v_s_3822_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3835_; 
v___x_3832_ = l_Lean_Parser_ParserState_keepTop(v_stxStack_3824_, v_startStackSize_3823_);
v___x_3833_ = lean_box(0);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 4, v___x_3833_);
lean_ctor_set(v___x_3830_, 0, v___x_3832_);
v___x_3835_ = v___x_3830_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_lhsPrec_3825_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_pos_3826_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_cache_3827_);
lean_ctor_set(v_reuseFailAlloc_3836_, 4, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3836_, 5, v_recoveredErrors_3828_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* v_s_3839_, lean_object* v_startStackSize_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_Parser_ParserState_keepLatest(v_s_3839_, v_startStackSize_3840_);
lean_dec(v_startStackSize_3840_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* v_s_3842_, lean_object* v_startStackSize_3843_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Lean_Parser_ParserState_keepLatest(v_s_3842_, v_startStackSize_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* v_s_3845_, lean_object* v_startStackSize_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_Parser_ParserState_replaceLongest(v_s_3845_, v_startStackSize_3846_);
lean_dec(v_startStackSize_3846_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* v_s_3849_){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = ((lean_object*)(l_Lean_Parser_invalidLongestMatchParser___closed__0));
v___x_3851_ = l_Lean_Parser_ParserState_mkError(v_s_3849_, v___x_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* v_left_x3f_3852_, lean_object* v_startLhsPrec_3853_, lean_object* v_p_3854_, lean_object* v_c_3855_, lean_object* v_s_3856_){
_start:
{
lean_object* v___y_3858_; lean_object* v_s_3859_; lean_object* v_stxStack_3872_; lean_object* v_pos_3873_; lean_object* v_cache_3874_; lean_object* v_errorMsg_3875_; lean_object* v_recoveredErrors_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3889_; 
v_stxStack_3872_ = lean_ctor_get(v_s_3856_, 0);
v_pos_3873_ = lean_ctor_get(v_s_3856_, 2);
v_cache_3874_ = lean_ctor_get(v_s_3856_, 3);
v_errorMsg_3875_ = lean_ctor_get(v_s_3856_, 4);
v_recoveredErrors_3876_ = lean_ctor_get(v_s_3856_, 5);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_s_3856_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_s_3856_, 1);
lean_dec(v_unused_3890_);
v___x_3878_ = v_s_3856_;
v_isShared_3879_ = v_isSharedCheck_3889_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_recoveredErrors_3876_);
lean_inc(v_errorMsg_3875_);
lean_inc(v_cache_3874_);
lean_inc(v_pos_3873_);
lean_inc(v_stxStack_3872_);
lean_dec(v_s_3856_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3889_;
goto v_resetjp_3877_;
}
v___jp_3857_:
{
lean_object* v_s_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_s_3860_ = lean_apply_2(v_p_3854_, v_c_3855_, v_s_3859_);
v___x_3861_ = l_Lean_Parser_ParserState_stackSize(v_s_3860_);
v___x_3862_ = lean_unsigned_to_nat(1u);
v___x_3863_ = lean_nat_add(v___y_3858_, v___x_3862_);
v___x_3864_ = lean_nat_dec_eq(v___x_3861_, v___x_3863_);
lean_dec(v___x_3863_);
lean_dec(v___x_3861_);
if (v___x_3864_ == 0)
{
lean_object* v_errorMsg_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v_errorMsg_3865_ = lean_ctor_get(v_s_3860_, 4);
lean_inc(v_errorMsg_3865_);
v___x_3866_ = lean_box(0);
v___x_3867_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3865_, v___x_3866_);
lean_dec(v_errorMsg_3865_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3868_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3860_, v___y_3858_);
lean_dec(v___y_3858_);
v___x_3869_ = lean_box(0);
v___x_3870_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3868_, v___x_3869_);
return v___x_3870_;
}
else
{
lean_object* v___x_3871_; 
lean_dec(v___y_3858_);
v___x_3871_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3860_);
return v___x_3871_;
}
}
else
{
lean_dec(v___y_3858_);
return v_s_3860_;
}
}
v_resetjp_3877_:
{
lean_object* v___y_3881_; 
if (lean_obj_tag(v_left_x3f_3852_) == 0)
{
lean_object* v___x_3888_; 
lean_dec(v_startLhsPrec_3853_);
v___x_3888_ = l_Lean_Parser_maxPrec;
v___y_3881_ = v___x_3888_;
goto v___jp_3880_;
}
else
{
v___y_3881_ = v_startLhsPrec_3853_;
goto v___jp_3880_;
}
v___jp_3880_:
{
lean_object* v_s_3883_; 
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v___y_3881_);
v_s_3883_ = v___x_3878_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_stxStack_3872_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___y_3881_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_pos_3873_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v_cache_3874_);
lean_ctor_set(v_reuseFailAlloc_3887_, 4, v_errorMsg_3875_);
lean_ctor_set(v_reuseFailAlloc_3887_, 5, v_recoveredErrors_3876_);
v_s_3883_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v_startSize_3884_; 
v_startSize_3884_ = l_Lean_Parser_ParserState_stackSize(v_s_3883_);
if (lean_obj_tag(v_left_x3f_3852_) == 1)
{
lean_object* v_val_3885_; lean_object* v_s_3886_; 
v_val_3885_ = lean_ctor_get(v_left_x3f_3852_, 0);
lean_inc(v_val_3885_);
lean_dec_ref_known(v_left_x3f_3852_, 1);
v_s_3886_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3883_, v_val_3885_);
v___y_3858_ = v_startSize_3884_;
v_s_3859_ = v_s_3886_;
goto v___jp_3857_;
}
else
{
lean_dec(v_left_x3f_3852_);
v___y_3858_ = v_startSize_3884_;
v_s_3859_ = v_s_3883_;
goto v___jp_3857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3891_, lean_object* v_prio_3892_){
_start:
{
lean_object* v_pos_3893_; lean_object* v_errorMsg_3894_; lean_object* v___y_3896_; 
v_pos_3893_ = lean_ctor_get(v_s_3891_, 2);
v_errorMsg_3894_ = lean_ctor_get(v_s_3891_, 4);
if (lean_obj_tag(v_errorMsg_3894_) == 0)
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_unsigned_to_nat(1u);
v___y_3896_ = v___x_3899_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_unsigned_to_nat(0u);
v___y_3896_ = v___x_3900_;
goto v___jp_3895_;
}
v___jp_3895_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___y_3896_);
lean_ctor_set(v___x_3897_, 1, v_prio_3892_);
lean_inc(v_pos_3893_);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v_pos_3893_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
return v___x_3898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3901_, lean_object* v_prio_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3901_, v_prio_3902_);
lean_dec_ref(v_s_3901_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3904_, lean_object* v_startSize_3905_, lean_object* v_startLhsPrec_3906_, lean_object* v_startPos_3907_, lean_object* v_prevPrio_3908_, lean_object* v_prio_3909_, lean_object* v_p_3910_, lean_object* v_c_3911_, lean_object* v_s_3912_){
_start:
{
lean_object* v_lhsPrec_3913_; lean_object* v_pos_3914_; lean_object* v_errorMsg_3915_; lean_object* v_previousScore_3916_; lean_object* v_fst_3917_; lean_object* v_snd_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3974_; 
v_lhsPrec_3913_ = lean_ctor_get(v_s_3912_, 1);
lean_inc(v_lhsPrec_3913_);
v_pos_3914_ = lean_ctor_get(v_s_3912_, 2);
lean_inc(v_pos_3914_);
v_errorMsg_3915_ = lean_ctor_get(v_s_3912_, 4);
lean_inc(v_errorMsg_3915_);
lean_inc(v_prevPrio_3908_);
v_previousScore_3916_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3912_, v_prevPrio_3908_);
v_fst_3917_ = lean_ctor_get(v_previousScore_3916_, 0);
v_snd_3918_ = lean_ctor_get(v_previousScore_3916_, 1);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_previousScore_3916_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3920_ = v_previousScore_3916_;
v_isShared_3921_ = v_isSharedCheck_3974_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_snd_3918_);
lean_inc(v_fst_3917_);
lean_dec(v_previousScore_3916_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3974_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v_prevSize_3922_; lean_object* v_s_3923_; lean_object* v_s_3924_; lean_object* v___x_3933_; lean_object* v_fst_3934_; lean_object* v_snd_3935_; uint8_t v___x_3936_; 
v_prevSize_3922_ = l_Lean_Parser_ParserState_stackSize(v_s_3912_);
v_s_3923_ = l_Lean_Parser_ParserState_restore(v_s_3912_, v_prevSize_3922_, v_startPos_3907_);
v_s_3924_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3904_, v_startLhsPrec_3906_, v_p_3910_, v_c_3911_, v_s_3923_);
lean_inc(v_prio_3909_);
v___x_3933_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3924_, v_prio_3909_);
v_fst_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_fst_3934_);
v_snd_3935_ = lean_ctor_get(v___x_3933_, 1);
lean_inc(v_snd_3935_);
lean_dec_ref(v___x_3933_);
v___x_3936_ = lean_nat_dec_lt(v_fst_3917_, v_fst_3934_);
if (v___x_3936_ == 0)
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_eq(v_fst_3917_, v_fst_3934_);
lean_dec(v_fst_3934_);
lean_dec(v_fst_3917_);
if (v___x_3937_ == 0)
{
lean_dec(v_snd_3935_);
lean_del_object(v___x_3920_);
lean_dec(v_snd_3918_);
lean_dec(v_prio_3909_);
goto v___jp_3930_;
}
else
{
lean_object* v_fst_3938_; lean_object* v_snd_3939_; lean_object* v_fst_3940_; lean_object* v_snd_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3973_; 
v_fst_3938_ = lean_ctor_get(v_snd_3918_, 0);
lean_inc(v_fst_3938_);
v_snd_3939_ = lean_ctor_get(v_snd_3918_, 1);
lean_inc(v_snd_3939_);
lean_dec(v_snd_3918_);
v_fst_3940_ = lean_ctor_get(v_snd_3935_, 0);
v_snd_3941_ = lean_ctor_get(v_snd_3935_, 1);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_snd_3935_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3943_ = v_snd_3935_;
v_isShared_3944_ = v_isSharedCheck_3973_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_snd_3941_);
lean_inc(v_fst_3940_);
lean_dec(v_snd_3935_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3973_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
uint8_t v___x_3945_; 
v___x_3945_ = lean_nat_dec_lt(v_fst_3938_, v_fst_3940_);
if (v___x_3945_ == 0)
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_eq(v_fst_3938_, v_fst_3940_);
lean_dec(v_fst_3940_);
lean_dec(v_fst_3938_);
if (v___x_3946_ == 0)
{
lean_del_object(v___x_3943_);
lean_dec(v_snd_3941_);
lean_dec(v_snd_3939_);
lean_del_object(v___x_3920_);
lean_dec(v_prio_3909_);
goto v___jp_3930_;
}
else
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_nat_dec_lt(v_snd_3939_, v_snd_3941_);
if (v___x_3947_ == 0)
{
uint8_t v___x_3948_; 
lean_del_object(v___x_3920_);
v___x_3948_ = lean_nat_dec_eq(v_snd_3939_, v_snd_3941_);
lean_dec(v_snd_3941_);
lean_dec(v_snd_3939_);
if (v___x_3948_ == 0)
{
lean_del_object(v___x_3943_);
lean_dec(v_prio_3909_);
goto v___jp_3930_;
}
else
{
lean_dec(v_pos_3914_);
lean_dec(v_prevPrio_3908_);
if (lean_obj_tag(v_errorMsg_3915_) == 0)
{
lean_object* v_stxStack_3949_; lean_object* v_lhsPrec_3950_; lean_object* v_pos_3951_; lean_object* v_cache_3952_; lean_object* v_errorMsg_3953_; lean_object* v_recoveredErrors_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v_prevSize_3922_);
v_stxStack_3949_ = lean_ctor_get(v_s_3924_, 0);
v_lhsPrec_3950_ = lean_ctor_get(v_s_3924_, 1);
v_pos_3951_ = lean_ctor_get(v_s_3924_, 2);
v_cache_3952_ = lean_ctor_get(v_s_3924_, 3);
v_errorMsg_3953_ = lean_ctor_get(v_s_3924_, 4);
v_recoveredErrors_3954_ = lean_ctor_get(v_s_3924_, 5);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_s_3924_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3956_ = v_s_3924_;
v_isShared_3957_ = v_isSharedCheck_3967_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_recoveredErrors_3954_);
lean_inc(v_errorMsg_3953_);
lean_inc(v_cache_3952_);
lean_inc(v_pos_3951_);
lean_inc(v_lhsPrec_3950_);
lean_inc(v_stxStack_3949_);
lean_dec(v_s_3924_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3967_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___y_3959_; uint8_t v___x_3966_; 
v___x_3966_ = lean_nat_dec_le(v_lhsPrec_3950_, v_lhsPrec_3913_);
if (v___x_3966_ == 0)
{
lean_dec(v_lhsPrec_3950_);
v___y_3959_ = v_lhsPrec_3913_;
goto v___jp_3958_;
}
else
{
lean_dec(v_lhsPrec_3913_);
v___y_3959_ = v_lhsPrec_3950_;
goto v___jp_3958_;
}
v___jp_3958_:
{
lean_object* v___x_3961_; 
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___y_3959_);
v___x_3961_ = v___x_3956_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_stxStack_3949_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v___y_3959_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_pos_3951_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_cache_3952_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v_errorMsg_3953_);
lean_ctor_set(v_reuseFailAlloc_3965_, 5, v_recoveredErrors_3954_);
v___x_3961_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3963_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 1, v_prio_3909_);
lean_ctor_set(v___x_3943_, 0, v___x_3961_);
v___x_3963_ = v___x_3943_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_prio_3909_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
}
else
{
lean_object* v_val_3968_; lean_object* v___x_3969_; lean_object* v___x_3971_; 
lean_dec(v_lhsPrec_3913_);
v_val_3968_ = lean_ctor_get(v_errorMsg_3915_, 0);
lean_inc(v_val_3968_);
lean_dec_ref_known(v_errorMsg_3915_, 1);
v___x_3969_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3924_, v_prevSize_3922_, v_val_3968_);
lean_dec(v_prevSize_3922_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 1, v_prio_3909_);
lean_ctor_set(v___x_3943_, 0, v___x_3969_);
v___x_3971_ = v___x_3943_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_prio_3909_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
lean_del_object(v___x_3943_);
lean_dec(v_snd_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_prevSize_3922_);
lean_dec(v_errorMsg_3915_);
lean_dec(v_pos_3914_);
lean_dec(v_lhsPrec_3913_);
lean_dec(v_prevPrio_3908_);
goto v___jp_3925_;
}
}
}
else
{
lean_del_object(v___x_3943_);
lean_dec(v_snd_3941_);
lean_dec(v_fst_3940_);
lean_dec(v_snd_3939_);
lean_dec(v_fst_3938_);
lean_dec(v_prevSize_3922_);
lean_dec(v_errorMsg_3915_);
lean_dec(v_pos_3914_);
lean_dec(v_lhsPrec_3913_);
lean_dec(v_prevPrio_3908_);
goto v___jp_3925_;
}
}
}
}
else
{
lean_dec(v_snd_3935_);
lean_dec(v_fst_3934_);
lean_dec(v_prevSize_3922_);
lean_dec(v_snd_3918_);
lean_dec(v_fst_3917_);
lean_dec(v_errorMsg_3915_);
lean_dec(v_pos_3914_);
lean_dec(v_lhsPrec_3913_);
lean_dec(v_prevPrio_3908_);
goto v___jp_3925_;
}
v___jp_3925_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = l_Lean_Parser_ParserState_keepNewError(v_s_3924_, v_startSize_3905_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 1, v_prio_3909_);
lean_ctor_set(v___x_3920_, 0, v___x_3926_);
v___x_3928_ = v___x_3920_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_prio_3909_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
v___jp_3930_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3924_, v_prevSize_3922_, v_pos_3914_, v_errorMsg_3915_, v_lhsPrec_3913_);
lean_dec(v_prevSize_3922_);
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
lean_ctor_set(v___x_3932_, 1, v_prevPrio_3908_);
return v___x_3932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3975_, lean_object* v_startSize_3976_, lean_object* v_startLhsPrec_3977_, lean_object* v_startPos_3978_, lean_object* v_prevPrio_3979_, lean_object* v_prio_3980_, lean_object* v_p_3981_, lean_object* v_c_3982_, lean_object* v_s_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3975_, v_startSize_3976_, v_startLhsPrec_3977_, v_startPos_3978_, v_prevPrio_3979_, v_prio_3980_, v_p_3981_, v_c_3982_, v_s_3983_);
lean_dec(v_startSize_3976_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3985_, lean_object* v_s_3986_){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3987_ = lean_unsigned_to_nat(1u);
v___x_3988_ = lean_nat_add(v_startSize_3985_, v___x_3987_);
v___x_3989_ = l_Lean_Parser_ParserState_stackSize(v_s_3986_);
v___x_3990_ = lean_nat_dec_lt(v___x_3988_, v___x_3989_);
lean_dec(v___x_3989_);
lean_dec(v___x_3988_);
if (v___x_3990_ == 0)
{
return v_s_3986_;
}
else
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3992_ = l_Lean_Parser_ParserState_mkNode(v_s_3986_, v___x_3991_, v_startSize_3985_);
return v___x_3992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3993_, lean_object* v_s_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3993_, v_s_3994_);
lean_dec(v_startSize_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3996_, lean_object* v_startSize_3997_, lean_object* v_startLhsPrec_3998_, lean_object* v_startPos_3999_, lean_object* v_prevPrio_4000_, lean_object* v_ps_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
if (lean_obj_tag(v_ps_4001_) == 0)
{
lean_object* v___x_4004_; 
lean_dec_ref(v_a_4002_);
lean_dec(v_prevPrio_4000_);
lean_dec(v_startPos_3999_);
lean_dec(v_startLhsPrec_3998_);
lean_dec(v_left_x3f_3996_);
v___x_4004_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3997_, v_a_4003_);
return v___x_4004_;
}
else
{
lean_object* v_head_4005_; lean_object* v_fst_4006_; lean_object* v_tail_4007_; lean_object* v_snd_4008_; lean_object* v_fn_4009_; lean_object* v___x_4010_; lean_object* v_fst_4011_; lean_object* v_snd_4012_; 
v_head_4005_ = lean_ctor_get(v_ps_4001_, 0);
lean_inc(v_head_4005_);
v_fst_4006_ = lean_ctor_get(v_head_4005_, 0);
lean_inc(v_fst_4006_);
v_tail_4007_ = lean_ctor_get(v_ps_4001_, 1);
lean_inc(v_tail_4007_);
lean_dec_ref_known(v_ps_4001_, 2);
v_snd_4008_ = lean_ctor_get(v_head_4005_, 1);
lean_inc(v_snd_4008_);
lean_dec(v_head_4005_);
v_fn_4009_ = lean_ctor_get(v_fst_4006_, 1);
lean_inc_ref(v_fn_4009_);
lean_dec(v_fst_4006_);
lean_inc_ref(v_a_4002_);
lean_inc(v_startPos_3999_);
lean_inc(v_startLhsPrec_3998_);
lean_inc(v_left_x3f_3996_);
v___x_4010_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3996_, v_startSize_3997_, v_startLhsPrec_3998_, v_startPos_3999_, v_prevPrio_4000_, v_snd_4008_, v_fn_4009_, v_a_4002_, v_a_4003_);
v_fst_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_fst_4011_);
v_snd_4012_ = lean_ctor_get(v___x_4010_, 1);
lean_inc(v_snd_4012_);
lean_dec_ref(v___x_4010_);
v_prevPrio_4000_ = v_snd_4012_;
v_ps_4001_ = v_tail_4007_;
v_a_4003_ = v_fst_4011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_4014_, lean_object* v_startSize_4015_, lean_object* v_startLhsPrec_4016_, lean_object* v_startPos_4017_, lean_object* v_prevPrio_4018_, lean_object* v_ps_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_4014_, v_startSize_4015_, v_startLhsPrec_4016_, v_startPos_4017_, v_prevPrio_4018_, v_ps_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_startSize_4015_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_4023_, lean_object* v_startSize_4024_, lean_object* v_startLhsPrec_4025_, lean_object* v_startPos_4026_, lean_object* v_prevPrio_4027_, lean_object* v_ps_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_4023_, v_startSize_4024_, v_startLhsPrec_4025_, v_startPos_4026_, v_prevPrio_4027_, v_ps_4028_, v_a_4029_, v_a_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_4032_, lean_object* v_startSize_4033_, lean_object* v_startLhsPrec_4034_, lean_object* v_startPos_4035_, lean_object* v_prevPrio_4036_, lean_object* v_ps_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_4032_, v_startSize_4033_, v_startLhsPrec_4034_, v_startPos_4035_, v_prevPrio_4036_, v_ps_4037_, v_a_4038_, v_a_4039_);
lean_dec(v_startSize_4033_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_4042_, lean_object* v_x_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_){
_start:
{
if (lean_obj_tag(v_x_4043_) == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref(v_a_4044_);
lean_dec(v_left_x3f_4042_);
v___x_4046_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_4047_ = l_Lean_Parser_ParserState_mkError(v_a_4045_, v___x_4046_);
return v___x_4047_;
}
else
{
lean_object* v_tail_4048_; 
v_tail_4048_ = lean_ctor_get(v_x_4043_, 1);
if (lean_obj_tag(v_tail_4048_) == 0)
{
lean_object* v_head_4049_; lean_object* v_fst_4050_; lean_object* v_lhsPrec_4051_; lean_object* v_fn_4052_; lean_object* v___x_4053_; 
v_head_4049_ = lean_ctor_get(v_x_4043_, 0);
lean_inc(v_head_4049_);
lean_dec_ref_known(v_x_4043_, 2);
v_fst_4050_ = lean_ctor_get(v_head_4049_, 0);
lean_inc(v_fst_4050_);
lean_dec(v_head_4049_);
v_lhsPrec_4051_ = lean_ctor_get(v_a_4045_, 1);
lean_inc(v_lhsPrec_4051_);
v_fn_4052_ = lean_ctor_get(v_fst_4050_, 1);
lean_inc_ref(v_fn_4052_);
lean_dec(v_fst_4050_);
v___x_4053_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_4042_, v_lhsPrec_4051_, v_fn_4052_, v_a_4044_, v_a_4045_);
return v___x_4053_;
}
else
{
lean_object* v_head_4054_; lean_object* v_fst_4055_; lean_object* v_lhsPrec_4056_; lean_object* v_pos_4057_; lean_object* v_snd_4058_; lean_object* v_fn_4059_; lean_object* v_startSize_4060_; lean_object* v_s_4061_; lean_object* v___x_4062_; 
lean_inc(v_tail_4048_);
v_head_4054_ = lean_ctor_get(v_x_4043_, 0);
lean_inc(v_head_4054_);
lean_dec_ref_known(v_x_4043_, 2);
v_fst_4055_ = lean_ctor_get(v_head_4054_, 0);
lean_inc(v_fst_4055_);
v_lhsPrec_4056_ = lean_ctor_get(v_a_4045_, 1);
lean_inc_n(v_lhsPrec_4056_, 2);
v_pos_4057_ = lean_ctor_get(v_a_4045_, 2);
lean_inc(v_pos_4057_);
v_snd_4058_ = lean_ctor_get(v_head_4054_, 1);
lean_inc(v_snd_4058_);
lean_dec(v_head_4054_);
v_fn_4059_ = lean_ctor_get(v_fst_4055_, 1);
lean_inc_ref(v_fn_4059_);
lean_dec(v_fst_4055_);
v_startSize_4060_ = l_Lean_Parser_ParserState_stackSize(v_a_4045_);
lean_inc_ref(v_a_4044_);
lean_inc(v_left_x3f_4042_);
v_s_4061_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_4042_, v_lhsPrec_4056_, v_fn_4059_, v_a_4044_, v_a_4045_);
v___x_4062_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_4042_, v_startSize_4060_, v_lhsPrec_4056_, v_pos_4057_, v_snd_4058_, v_tail_4048_, v_a_4044_, v_s_4061_);
lean_dec(v_startSize_4060_);
return v___x_4062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_4064_, lean_object* v_x_4065_, lean_object* v_x_4066_){
_start:
{
if (lean_obj_tag(v_x_4064_) == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec_ref(v_x_4065_);
v___x_4067_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_4068_ = l_Lean_Parser_ParserState_mkError(v_x_4066_, v___x_4067_);
return v___x_4068_;
}
else
{
lean_object* v_tail_4069_; 
v_tail_4069_ = lean_ctor_get(v_x_4064_, 1);
if (lean_obj_tag(v_tail_4069_) == 0)
{
lean_object* v_head_4070_; lean_object* v_fn_4071_; lean_object* v___x_4072_; 
v_head_4070_ = lean_ctor_get(v_x_4064_, 0);
lean_inc(v_head_4070_);
lean_dec_ref_known(v_x_4064_, 2);
v_fn_4071_ = lean_ctor_get(v_head_4070_, 1);
lean_inc_ref(v_fn_4071_);
lean_dec(v_head_4070_);
v___x_4072_ = lean_apply_2(v_fn_4071_, v_x_4065_, v_x_4066_);
return v___x_4072_;
}
else
{
lean_object* v_head_4073_; lean_object* v_fn_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_inc(v_tail_4069_);
v_head_4073_ = lean_ctor_get(v_x_4064_, 0);
lean_inc(v_head_4073_);
lean_dec_ref_known(v_x_4064_, 2);
v_fn_4074_ = lean_ctor_get(v_head_4073_, 1);
lean_inc_ref(v_fn_4074_);
lean_dec(v_head_4073_);
v___x_4075_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_4075_, 0, v_tail_4069_);
v___x_4076_ = l_Lean_Parser_orelseFn(v_fn_4074_, v___x_4075_, v_x_4065_, v_x_4066_);
return v___x_4076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_4077_, lean_object* v_c_4078_, lean_object* v_s_4079_){
_start:
{
lean_object* v_toCacheableParserContext_4080_; lean_object* v_savedPos_x3f_4081_; 
v_toCacheableParserContext_4080_ = lean_ctor_get(v_c_4078_, 2);
v_savedPos_x3f_4081_ = lean_ctor_get(v_toCacheableParserContext_4080_, 2);
lean_inc(v_savedPos_x3f_4081_);
if (lean_obj_tag(v_savedPos_x3f_4081_) == 0)
{
lean_dec_ref(v_c_4078_);
lean_dec_ref(v_errorMsg_4077_);
return v_s_4079_;
}
else
{
lean_object* v_toInputContext_4082_; lean_object* v_val_4083_; lean_object* v_fileMap_4084_; lean_object* v_pos_4085_; lean_object* v_savedPos_4086_; lean_object* v_pos_4087_; lean_object* v_column_4088_; lean_object* v_column_4089_; uint8_t v___x_4090_; 
v_toInputContext_4082_ = lean_ctor_get(v_c_4078_, 0);
lean_inc_ref(v_toInputContext_4082_);
lean_dec_ref(v_c_4078_);
v_val_4083_ = lean_ctor_get(v_savedPos_x3f_4081_, 0);
lean_inc(v_val_4083_);
lean_dec_ref_known(v_savedPos_x3f_4081_, 1);
v_fileMap_4084_ = lean_ctor_get(v_toInputContext_4082_, 2);
lean_inc_ref_n(v_fileMap_4084_, 2);
lean_dec_ref(v_toInputContext_4082_);
v_pos_4085_ = lean_ctor_get(v_s_4079_, 2);
v_savedPos_4086_ = l_Lean_FileMap_toPosition(v_fileMap_4084_, v_val_4083_);
lean_dec(v_val_4083_);
v_pos_4087_ = l_Lean_FileMap_toPosition(v_fileMap_4084_, v_pos_4085_);
v_column_4088_ = lean_ctor_get(v_pos_4087_, 1);
lean_inc(v_column_4088_);
lean_dec_ref(v_pos_4087_);
v_column_4089_ = lean_ctor_get(v_savedPos_4086_, 1);
lean_inc(v_column_4089_);
lean_dec_ref(v_savedPos_4086_);
v___x_4090_ = lean_nat_dec_eq(v_column_4088_, v_column_4089_);
lean_dec(v_column_4089_);
lean_dec(v_column_4088_);
if (v___x_4090_ == 0)
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_Parser_ParserState_mkError(v_s_4079_, v_errorMsg_4077_);
return v___x_4091_;
}
else
{
lean_dec_ref(v_errorMsg_4077_);
return v_s_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_4092_){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4093_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4094_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_4094_, 0, v_errorMsg_4092_);
v___x_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
return v___x_4095_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4104_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4105_ = l_Lean_addBuiltinDocString(v___x_4103_, v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4106_;
v_res_4106_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
stack->m_obj
 = v_res_4106_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4109_, lean_object* v_c_4110_, lean_object* v_s_4111_){
_start:
{
lean_object* v_toCacheableParserContext_4112_; lean_object* v_savedPos_x3f_4113_; 
v_toCacheableParserContext_4112_ = lean_ctor_get(v_c_4110_, 2);
v_savedPos_x3f_4113_ = lean_ctor_get(v_toCacheableParserContext_4112_, 2);
lean_inc(v_savedPos_x3f_4113_);
if (lean_obj_tag(v_savedPos_x3f_4113_) == 0)
{
lean_dec_ref(v_c_4110_);
lean_dec_ref(v_errorMsg_4109_);
return v_s_4111_;
}
else
{
lean_object* v_toInputContext_4114_; lean_object* v_val_4115_; lean_object* v_fileMap_4116_; lean_object* v_pos_4117_; lean_object* v_savedPos_4118_; lean_object* v_column_4119_; lean_object* v_pos_4120_; lean_object* v_column_4121_; uint8_t v___x_4122_; 
v_toInputContext_4114_ = lean_ctor_get(v_c_4110_, 0);
lean_inc_ref(v_toInputContext_4114_);
lean_dec_ref(v_c_4110_);
v_val_4115_ = lean_ctor_get(v_savedPos_x3f_4113_, 0);
lean_inc(v_val_4115_);
lean_dec_ref_known(v_savedPos_x3f_4113_, 1);
v_fileMap_4116_ = lean_ctor_get(v_toInputContext_4114_, 2);
lean_inc_ref_n(v_fileMap_4116_, 2);
lean_dec_ref(v_toInputContext_4114_);
v_pos_4117_ = lean_ctor_get(v_s_4111_, 2);
v_savedPos_4118_ = l_Lean_FileMap_toPosition(v_fileMap_4116_, v_val_4115_);
lean_dec(v_val_4115_);
v_column_4119_ = lean_ctor_get(v_savedPos_4118_, 1);
lean_inc(v_column_4119_);
lean_dec_ref(v_savedPos_4118_);
v_pos_4120_ = l_Lean_FileMap_toPosition(v_fileMap_4116_, v_pos_4117_);
v_column_4121_ = lean_ctor_get(v_pos_4120_, 1);
lean_inc(v_column_4121_);
lean_dec_ref(v_pos_4120_);
v___x_4122_ = lean_nat_dec_le(v_column_4119_, v_column_4121_);
lean_dec(v_column_4121_);
lean_dec(v_column_4119_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_Parser_ParserState_mkError(v_s_4111_, v_errorMsg_4109_);
return v___x_4123_;
}
else
{
lean_dec_ref(v_errorMsg_4109_);
return v_s_4111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4124_){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4126_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4126_, 0, v_errorMsg_4124_);
v___x_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
return v___x_4127_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4135_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4136_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4137_ = l_Lean_addBuiltinDocString(v___x_4135_, v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4138_;
v_res_4138_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
stack->m_obj
 = v_res_4138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4141_, lean_object* v_c_4142_, lean_object* v_s_4143_){
_start:
{
lean_object* v_toCacheableParserContext_4144_; lean_object* v_savedPos_x3f_4145_; 
v_toCacheableParserContext_4144_ = lean_ctor_get(v_c_4142_, 2);
v_savedPos_x3f_4145_ = lean_ctor_get(v_toCacheableParserContext_4144_, 2);
lean_inc(v_savedPos_x3f_4145_);
if (lean_obj_tag(v_savedPos_x3f_4145_) == 0)
{
lean_dec_ref(v_c_4142_);
lean_dec_ref(v_errorMsg_4141_);
return v_s_4143_;
}
else
{
lean_object* v_toInputContext_4146_; lean_object* v_val_4147_; lean_object* v_fileMap_4148_; lean_object* v_pos_4149_; lean_object* v_savedPos_4150_; lean_object* v_column_4151_; lean_object* v_pos_4152_; lean_object* v_column_4153_; uint8_t v___x_4154_; 
v_toInputContext_4146_ = lean_ctor_get(v_c_4142_, 0);
lean_inc_ref(v_toInputContext_4146_);
lean_dec_ref(v_c_4142_);
v_val_4147_ = lean_ctor_get(v_savedPos_x3f_4145_, 0);
lean_inc(v_val_4147_);
lean_dec_ref_known(v_savedPos_x3f_4145_, 1);
v_fileMap_4148_ = lean_ctor_get(v_toInputContext_4146_, 2);
lean_inc_ref_n(v_fileMap_4148_, 2);
lean_dec_ref(v_toInputContext_4146_);
v_pos_4149_ = lean_ctor_get(v_s_4143_, 2);
v_savedPos_4150_ = l_Lean_FileMap_toPosition(v_fileMap_4148_, v_val_4147_);
lean_dec(v_val_4147_);
v_column_4151_ = lean_ctor_get(v_savedPos_4150_, 1);
lean_inc(v_column_4151_);
lean_dec_ref(v_savedPos_4150_);
v_pos_4152_ = l_Lean_FileMap_toPosition(v_fileMap_4148_, v_pos_4149_);
v_column_4153_ = lean_ctor_get(v_pos_4152_, 1);
lean_inc(v_column_4153_);
lean_dec_ref(v_pos_4152_);
v___x_4154_ = lean_nat_dec_lt(v_column_4151_, v_column_4153_);
lean_dec(v_column_4153_);
lean_dec(v_column_4151_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Lean_Parser_ParserState_mkError(v_s_4143_, v_errorMsg_4141_);
return v___x_4155_;
}
else
{
lean_dec_ref(v_errorMsg_4141_);
return v_s_4143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4156_){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4157_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4158_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4158_, 0, v_errorMsg_4156_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
return v___x_4159_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4168_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4169_ = l_Lean_addBuiltinDocString(v___x_4167_, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4170_;
v_res_4170_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
stack->m_obj
 = v_res_4170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4173_, lean_object* v_c_4174_, lean_object* v_s_4175_){
_start:
{
lean_object* v_toCacheableParserContext_4176_; lean_object* v_savedPos_x3f_4177_; 
v_toCacheableParserContext_4176_ = lean_ctor_get(v_c_4174_, 2);
v_savedPos_x3f_4177_ = lean_ctor_get(v_toCacheableParserContext_4176_, 2);
lean_inc(v_savedPos_x3f_4177_);
if (lean_obj_tag(v_savedPos_x3f_4177_) == 0)
{
lean_dec_ref(v_c_4174_);
lean_dec_ref(v_errorMsg_4173_);
return v_s_4175_;
}
else
{
lean_object* v_toInputContext_4178_; lean_object* v_val_4179_; lean_object* v_fileMap_4180_; lean_object* v_pos_4181_; lean_object* v_savedPos_4182_; lean_object* v_pos_4183_; lean_object* v_line_4184_; lean_object* v_line_4185_; uint8_t v___x_4186_; 
v_toInputContext_4178_ = lean_ctor_get(v_c_4174_, 0);
lean_inc_ref(v_toInputContext_4178_);
lean_dec_ref(v_c_4174_);
v_val_4179_ = lean_ctor_get(v_savedPos_x3f_4177_, 0);
lean_inc(v_val_4179_);
lean_dec_ref_known(v_savedPos_x3f_4177_, 1);
v_fileMap_4180_ = lean_ctor_get(v_toInputContext_4178_, 2);
lean_inc_ref_n(v_fileMap_4180_, 2);
lean_dec_ref(v_toInputContext_4178_);
v_pos_4181_ = lean_ctor_get(v_s_4175_, 2);
v_savedPos_4182_ = l_Lean_FileMap_toPosition(v_fileMap_4180_, v_val_4179_);
lean_dec(v_val_4179_);
v_pos_4183_ = l_Lean_FileMap_toPosition(v_fileMap_4180_, v_pos_4181_);
v_line_4184_ = lean_ctor_get(v_pos_4183_, 0);
lean_inc(v_line_4184_);
lean_dec_ref(v_pos_4183_);
v_line_4185_ = lean_ctor_get(v_savedPos_4182_, 0);
lean_inc(v_line_4185_);
lean_dec_ref(v_savedPos_4182_);
v___x_4186_ = lean_nat_dec_eq(v_line_4184_, v_line_4185_);
lean_dec(v_line_4185_);
lean_dec(v_line_4184_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Parser_ParserState_mkError(v_s_4175_, v_errorMsg_4173_);
return v___x_4187_;
}
else
{
lean_dec_ref(v_errorMsg_4173_);
return v_s_4175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4188_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4190_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4190_, 0, v_errorMsg_4188_);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4189_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
return v___x_4191_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4200_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4201_ = l_Lean_addBuiltinDocString(v___x_4199_, v___x_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4202_;
v_res_4202_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
stack->m_obj
 = v_res_4202_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4205_, lean_object* v_x_4206_){
_start:
{
lean_object* v_prec_4207_; lean_object* v_quotDepth_4208_; uint8_t v_suppressInsideQuot_4209_; lean_object* v_forbiddenTks_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4219_; 
v_prec_4207_ = lean_ctor_get(v_x_4206_, 0);
v_quotDepth_4208_ = lean_ctor_get(v_x_4206_, 1);
v_suppressInsideQuot_4209_ = lean_ctor_get_uint8(v_x_4206_, sizeof(void*)*4);
v_forbiddenTks_4210_ = lean_ctor_get(v_x_4206_, 3);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_x_4206_);
if (v_isSharedCheck_4219_ == 0)
{
lean_object* v_unused_4220_; 
v_unused_4220_ = lean_ctor_get(v_x_4206_, 2);
lean_dec(v_unused_4220_);
v___x_4212_ = v_x_4206_;
v_isShared_4213_ = v_isSharedCheck_4219_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_forbiddenTks_4210_);
lean_inc(v_quotDepth_4208_);
lean_inc(v_prec_4207_);
lean_dec(v_x_4206_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4219_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v_pos_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
v_pos_4214_ = lean_ctor_get(v___y_4205_, 2);
lean_inc(v_pos_4214_);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_pos_4214_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 2, v___x_4215_);
v___x_4217_ = v___x_4212_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_prec_4207_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_quotDepth_4208_);
lean_ctor_set(v_reuseFailAlloc_4218_, 2, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4218_, 3, v_forbiddenTks_4210_);
lean_ctor_set_uint8(v_reuseFailAlloc_4218_, sizeof(void*)*4, v_suppressInsideQuot_4209_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4221_, lean_object* v_x_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Parser_withPosition___lam__0(v___y_4221_, v_x_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___f_4227_; lean_object* v___x_4228_; 
lean_inc_ref(v___y_4226_);
v___f_4227_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4227_, 0, v___y_4226_);
v___x_4228_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4227_, v_fn_4224_, v___y_4225_, v___y_4226_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4229_){
_start:
{
lean_object* v_info_4230_; lean_object* v_fn_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4239_; 
v_info_4230_ = lean_ctor_get(v_p_4229_, 0);
v_fn_4231_ = lean_ctor_get(v_p_4229_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_p_4229_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4233_ = v_p_4229_;
v_isShared_4234_ = v_isSharedCheck_4239_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_fn_4231_);
lean_inc(v_info_4230_);
lean_dec(v_p_4229_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4239_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___f_4235_; lean_object* v___x_4237_; 
v___f_4235_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4235_, 0, v_fn_4231_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v___f_4235_);
v___x_4237_ = v___x_4233_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_info_4230_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v___f_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4248_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4249_ = l_Lean_addBuiltinDocString(v___x_4247_, v___x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4250_;
v_res_4250_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
stack->m_obj
 = v_res_4250_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4253_, lean_object* v_pos_4254_, lean_object* v_c_4255_){
_start:
{
uint8_t v___x_4256_; 
v___x_4256_ = l_Lean_Parser_checkTailLinebreak(v_prev_4253_);
if (v___x_4256_ == 0)
{
lean_dec(v_pos_4254_);
return v_c_4255_;
}
else
{
lean_object* v_prec_4257_; lean_object* v_quotDepth_4258_; uint8_t v_suppressInsideQuot_4259_; lean_object* v_forbiddenTks_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4268_; 
v_prec_4257_ = lean_ctor_get(v_c_4255_, 0);
v_quotDepth_4258_ = lean_ctor_get(v_c_4255_, 1);
v_suppressInsideQuot_4259_ = lean_ctor_get_uint8(v_c_4255_, sizeof(void*)*4);
v_forbiddenTks_4260_ = lean_ctor_get(v_c_4255_, 3);
v_isSharedCheck_4268_ = !lean_is_exclusive(v_c_4255_);
if (v_isSharedCheck_4268_ == 0)
{
lean_object* v_unused_4269_; 
v_unused_4269_ = lean_ctor_get(v_c_4255_, 2);
lean_dec(v_unused_4269_);
v___x_4262_ = v_c_4255_;
v_isShared_4263_ = v_isSharedCheck_4268_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_forbiddenTks_4260_);
lean_inc(v_quotDepth_4258_);
lean_inc(v_prec_4257_);
lean_dec(v_c_4255_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4268_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4264_, 0, v_pos_4254_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 2, v___x_4264_);
v___x_4266_ = v___x_4262_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_prec_4257_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_quotDepth_4258_);
lean_ctor_set(v_reuseFailAlloc_4267_, 2, v___x_4264_);
lean_ctor_set(v_reuseFailAlloc_4267_, 3, v_forbiddenTks_4260_);
lean_ctor_set_uint8(v_reuseFailAlloc_4267_, sizeof(void*)*4, v_suppressInsideQuot_4259_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4270_, lean_object* v_pos_4271_, lean_object* v_c_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4270_, v_pos_4271_, v_c_4272_);
lean_dec(v_prev_4270_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_stxStack_4277_; lean_object* v_pos_4278_; lean_object* v_prev_4279_; lean_object* v___f_4280_; lean_object* v___x_4281_; 
v_stxStack_4277_ = lean_ctor_get(v___y_4276_, 0);
v_pos_4278_ = lean_ctor_get(v___y_4276_, 2);
v_prev_4279_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4277_);
lean_inc(v_pos_4278_);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4280_, 0, v_prev_4279_);
lean_closure_set(v___f_4280_, 1, v_pos_4278_);
v___x_4281_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4280_, v_fn_4274_, v___y_4275_, v___y_4276_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4282_){
_start:
{
lean_object* v_info_4283_; lean_object* v_fn_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4292_; 
v_info_4283_ = lean_ctor_get(v_p_4282_, 0);
v_fn_4284_ = lean_ctor_get(v_p_4282_, 1);
v_isSharedCheck_4292_ = !lean_is_exclusive(v_p_4282_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4286_ = v_p_4282_;
v_isShared_4287_ = v_isSharedCheck_4292_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_fn_4284_);
lean_inc(v_info_4283_);
lean_dec(v_p_4282_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4292_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___f_4288_; lean_object* v___x_4290_; 
v___f_4288_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(v___f_4288_, 0, v_fn_4284_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 1, v___f_4288_);
v___x_4290_ = v___x_4286_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_info_4283_);
lean_ctor_set(v_reuseFailAlloc_4291_, 1, v___f_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4293_){
_start:
{
lean_object* v_prec_4294_; lean_object* v_quotDepth_4295_; uint8_t v_suppressInsideQuot_4296_; lean_object* v_forbiddenTks_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4305_; 
v_prec_4294_ = lean_ctor_get(v_x_4293_, 0);
v_quotDepth_4295_ = lean_ctor_get(v_x_4293_, 1);
v_suppressInsideQuot_4296_ = lean_ctor_get_uint8(v_x_4293_, sizeof(void*)*4);
v_forbiddenTks_4297_ = lean_ctor_get(v_x_4293_, 3);
v_isSharedCheck_4305_ = !lean_is_exclusive(v_x_4293_);
if (v_isSharedCheck_4305_ == 0)
{
lean_object* v_unused_4306_; 
v_unused_4306_ = lean_ctor_get(v_x_4293_, 2);
lean_dec(v_unused_4306_);
v___x_4299_ = v_x_4293_;
v_isShared_4300_ = v_isSharedCheck_4305_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_forbiddenTks_4297_);
lean_inc(v_quotDepth_4295_);
lean_inc(v_prec_4294_);
lean_dec(v_x_4293_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4305_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
v___x_4301_ = lean_box(0);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 2, v___x_4301_);
v___x_4303_ = v___x_4299_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_prec_4294_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_quotDepth_4295_);
lean_ctor_set(v_reuseFailAlloc_4304_, 2, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4304_, 3, v_forbiddenTks_4297_);
lean_ctor_set_uint8(v_reuseFailAlloc_4304_, sizeof(void*)*4, v_suppressInsideQuot_4296_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4308_){
_start:
{
lean_object* v___f_4309_; lean_object* v___x_4310_; 
v___f_4309_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4310_ = l_Lean_Parser_adaptCacheableContext(v___f_4309_, v_p_4308_);
return v___x_4310_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4318_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4319_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4320_ = l_Lean_addBuiltinDocString(v___x_4318_, v___x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4321_;
v_res_4321_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
stack->m_obj
 = v_res_4321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4324_, lean_object* v_c_4325_){
_start:
{
lean_object* v_prec_4326_; lean_object* v_quotDepth_4327_; uint8_t v_suppressInsideQuot_4328_; lean_object* v_savedPos_x3f_4329_; lean_object* v_forbiddenTks_4330_; uint8_t v___x_4331_; 
v_prec_4326_ = lean_ctor_get(v_c_4325_, 0);
v_quotDepth_4327_ = lean_ctor_get(v_c_4325_, 1);
v_suppressInsideQuot_4328_ = lean_ctor_get_uint8(v_c_4325_, sizeof(void*)*4);
v_savedPos_x3f_4329_ = lean_ctor_get(v_c_4325_, 2);
v_forbiddenTks_4330_ = lean_ctor_get(v_c_4325_, 3);
v___x_4331_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_4330_, v_tk_4324_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4339_; 
lean_inc_ref(v_forbiddenTks_4330_);
lean_inc(v_savedPos_x3f_4329_);
lean_inc(v_quotDepth_4327_);
lean_inc(v_prec_4326_);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_c_4325_);
if (v_isSharedCheck_4339_ == 0)
{
lean_object* v_unused_4340_; lean_object* v_unused_4341_; lean_object* v_unused_4342_; lean_object* v_unused_4343_; 
v_unused_4340_ = lean_ctor_get(v_c_4325_, 3);
lean_dec(v_unused_4340_);
v_unused_4341_ = lean_ctor_get(v_c_4325_, 2);
lean_dec(v_unused_4341_);
v_unused_4342_ = lean_ctor_get(v_c_4325_, 1);
lean_dec(v_unused_4342_);
v_unused_4343_ = lean_ctor_get(v_c_4325_, 0);
lean_dec(v_unused_4343_);
v___x_4333_ = v_c_4325_;
v_isShared_4334_ = v_isSharedCheck_4339_;
goto v_resetjp_4332_;
}
else
{
lean_dec(v_c_4325_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4339_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4335_; lean_object* v___x_4337_; 
v___x_4335_ = lean_array_push(v_forbiddenTks_4330_, v_tk_4324_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 3, v___x_4335_);
v___x_4337_ = v___x_4333_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_prec_4326_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_quotDepth_4327_);
lean_ctor_set(v_reuseFailAlloc_4338_, 2, v_savedPos_x3f_4329_);
lean_ctor_set(v_reuseFailAlloc_4338_, 3, v___x_4335_);
lean_ctor_set_uint8(v_reuseFailAlloc_4338_, sizeof(void*)*4, v_suppressInsideQuot_4328_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
else
{
lean_dec_ref(v_tk_4324_);
return v_c_4325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4344_, lean_object* v_p_4345_){
_start:
{
lean_object* v___f_4346_; lean_object* v___x_4347_; 
v___f_4346_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4346_, 0, v_tk_4344_);
v___x_4347_ = l_Lean_Parser_adaptCacheableContext(v___f_4346_, v_p_4345_);
return v___x_4347_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4356_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4357_ = l_Lean_addBuiltinDocString(v___x_4355_, v___x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4358_;
v_res_4358_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
stack->m_obj
 = v_res_4358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4360_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(lean_object* v_a_4361_, lean_object* v_as_4362_, size_t v_i_4363_, size_t v_stop_4364_){
_start:
{
uint8_t v___x_4365_; 
v___x_4365_ = lean_usize_dec_eq(v_i_4363_, v_stop_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = lean_array_uget_borrowed(v_as_4362_, v_i_4363_);
v___x_4367_ = lean_string_dec_eq(v___x_4366_, v_a_4361_);
if (v___x_4367_ == 0)
{
size_t v___x_4368_; size_t v___x_4369_; 
v___x_4368_ = ((size_t)1ULL);
v___x_4369_ = lean_usize_add(v_i_4363_, v___x_4368_);
v_i_4363_ = v___x_4369_;
goto _start;
}
else
{
return v___x_4367_;
}
}
else
{
uint8_t v___x_4371_; 
v___x_4371_ = 0;
return v___x_4371_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4361_ = stack[0].m_obj;
lean_object* v_as_4362_ = stack[1].m_obj;
size_t v_i_4363_ = stack[2].m_num;
size_t v_stop_4364_ = stack[3].m_num;
uint8_t v_res_4372_;
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4361_, v_as_4362_, v_i_4363_, v_stop_4364_);
stack->m_num = v_res_4372_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0___boxed(lean_object* v_a_4373_, lean_object* v_as_4374_, lean_object* v_i_4375_, lean_object* v_stop_4376_){
_start:
{
size_t v_i_boxed_4377_; size_t v_stop_boxed_4378_; uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_i_boxed_4377_ = lean_unbox_usize(v_i_4375_);
lean_dec(v_i_4375_);
v_stop_boxed_4378_ = lean_unbox_usize(v_stop_4376_);
lean_dec(v_stop_4376_);
v_res_4379_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4373_, v_as_4374_, v_i_boxed_4377_, v_stop_boxed_4378_);
lean_dec_ref(v_as_4374_);
lean_dec_ref(v_a_4373_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(lean_object* v_size_4381_, lean_object* v_as_4382_, size_t v_sz_4383_, size_t v_i_4384_, lean_object* v_b_4385_){
_start:
{
lean_object* v_a_4387_; uint8_t v___x_4391_; 
v___x_4391_ = lean_usize_dec_lt(v_i_4384_, v_sz_4383_);
if (v___x_4391_ == 0)
{
lean_dec(v_size_4381_);
return v_b_4385_;
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4395_; lean_object* v___y_4397_; uint8_t v___x_4402_; 
v_a_4392_ = lean_array_uget_borrowed(v_as_4382_, v_i_4384_);
v___x_4395_ = lean_unsigned_to_nat(0u);
v___x_4402_ = lean_nat_dec_lt(v___x_4395_, v_size_4381_);
if (v___x_4402_ == 0)
{
goto v___jp_4393_;
}
else
{
lean_object* v___x_4403_; uint8_t v___x_4404_; 
v___x_4403_ = lean_array_get_size(v_b_4385_);
v___x_4404_ = lean_nat_dec_le(v_size_4381_, v___x_4403_);
if (v___x_4404_ == 0)
{
v___y_4397_ = v___x_4403_;
goto v___jp_4396_;
}
else
{
lean_inc(v_size_4381_);
v___y_4397_ = v_size_4381_;
goto v___jp_4396_;
}
}
v___jp_4393_:
{
lean_object* v___x_4394_; 
lean_inc(v_a_4392_);
v___x_4394_ = lean_array_push(v_b_4385_, v_a_4392_);
v_a_4387_ = v___x_4394_;
goto v___jp_4386_;
}
v___jp_4396_:
{
uint8_t v___x_4398_; 
v___x_4398_ = lean_nat_dec_lt(v___x_4395_, v___y_4397_);
if (v___x_4398_ == 0)
{
lean_dec(v___y_4397_);
goto v___jp_4393_;
}
else
{
size_t v___x_4399_; size_t v___x_4400_; uint8_t v___x_4401_; 
v___x_4399_ = ((size_t)0ULL);
v___x_4400_ = lean_usize_of_nat(v___y_4397_);
lean_dec(v___y_4397_);
v___x_4401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4392_, v_b_4385_, v___x_4399_, v___x_4400_);
if (v___x_4401_ == 0)
{
goto v___jp_4393_;
}
else
{
v_a_4387_ = v_b_4385_;
goto v___jp_4386_;
}
}
}
}
v___jp_4386_:
{
size_t v___x_4388_; size_t v___x_4389_; 
v___x_4388_ = ((size_t)1ULL);
v___x_4389_ = lean_usize_add(v_i_4384_, v___x_4388_);
v_i_4384_ = v___x_4389_;
v_b_4385_ = v_a_4387_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_4381_ = stack[0].m_obj;
lean_object* v_as_4382_ = stack[1].m_obj;
size_t v_sz_4383_ = stack[2].m_num;
size_t v_i_4384_ = stack[3].m_num;
lean_object* v_b_4385_ = stack[4].m_obj;
lean_object* v_res_4405_;
v_res_4405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4381_, v_as_4382_, v_sz_4383_, v_i_4384_, v_b_4385_);
stack->m_obj
 = v_res_4405_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1___boxed(lean_object* v_size_4406_, lean_object* v_as_4407_, lean_object* v_sz_4408_, lean_object* v_i_4409_, lean_object* v_b_4410_){
_start:
{
size_t v_sz_boxed_4411_; size_t v_i_boxed_4412_; lean_object* v_res_4413_; 
v_sz_boxed_4411_ = lean_unbox_usize(v_sz_4408_);
lean_dec(v_sz_4408_);
v_i_boxed_4412_ = lean_unbox_usize(v_i_4409_);
lean_dec(v_i_4409_);
v_res_4413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4406_, v_as_4407_, v_sz_boxed_4411_, v_i_boxed_4412_, v_b_4410_);
lean_dec_ref(v_as_4407_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(lean_object* v_init_4414_, lean_object* v_tks_4415_){
_start:
{
lean_object* v_size_4416_; size_t v_sz_4417_; size_t v___x_4418_; lean_object* v___x_4419_; 
v_size_4416_ = lean_array_get_size(v_init_4414_);
v_sz_4417_ = lean_array_size(v_tks_4415_);
v___x_4418_ = ((size_t)0ULL);
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4416_, v_tks_4415_, v_sz_4417_, v___x_4418_, v_init_4414_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks___boxed(lean_object* v_init_4420_, lean_object* v_tks_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_init_4420_, v_tks_4421_);
lean_dec_ref(v_tks_4421_);
return v_res_4422_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__6));
v___x_4445_ = l_Lean_mkAtom(v___x_4444_);
return v___x_4445_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__8, &l_Lean_Parser_withForbiddens___auto__1___closed__8_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__8);
v___x_4447_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4448_ = lean_array_push(v___x_4447_, v___x_4446_);
return v___x_4448_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4459_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_4460_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4461_ = lean_array_push(v___x_4460_, v___x_4459_);
return v___x_4461_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4462_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__13, &l_Lean_Parser_withForbiddens___auto__1___closed__13_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__13);
v___x_4463_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__11));
v___x_4464_ = lean_box(2);
v___x_4465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
lean_ctor_set(v___x_4465_, 1, v___x_4463_);
lean_ctor_set(v___x_4465_, 2, v___x_4462_);
return v___x_4465_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__14, &l_Lean_Parser_withForbiddens___auto__1___closed__14_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__14);
v___x_4467_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__9, &l_Lean_Parser_withForbiddens___auto__1___closed__9_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__9);
v___x_4468_ = lean_array_push(v___x_4467_, v___x_4466_);
return v___x_4468_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4469_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__15, &l_Lean_Parser_withForbiddens___auto__1___closed__15_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__15);
v___x_4470_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__7));
v___x_4471_ = lean_box(2);
v___x_4472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
lean_ctor_set(v___x_4472_, 1, v___x_4470_);
lean_ctor_set(v___x_4472_, 2, v___x_4469_);
return v___x_4472_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4473_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__16, &l_Lean_Parser_withForbiddens___auto__1___closed__16_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__16);
v___x_4474_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4475_ = lean_array_push(v___x_4474_, v___x_4473_);
return v___x_4475_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4476_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__17, &l_Lean_Parser_withForbiddens___auto__1___closed__17_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__17);
v___x_4477_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_4478_ = lean_box(2);
v___x_4479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
lean_ctor_set(v___x_4479_, 1, v___x_4477_);
lean_ctor_set(v___x_4479_, 2, v___x_4476_);
return v___x_4479_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4480_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__18, &l_Lean_Parser_withForbiddens___auto__1___closed__18_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__18);
v___x_4481_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4482_ = lean_array_push(v___x_4481_, v___x_4480_);
return v___x_4482_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4483_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__19, &l_Lean_Parser_withForbiddens___auto__1___closed__19_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__19);
v___x_4484_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__5));
v___x_4485_ = lean_box(2);
v___x_4486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
lean_ctor_set(v___x_4486_, 1, v___x_4484_);
lean_ctor_set(v___x_4486_, 2, v___x_4483_);
return v___x_4486_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4487_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__20, &l_Lean_Parser_withForbiddens___auto__1___closed__20_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__20);
v___x_4488_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4489_ = lean_array_push(v___x_4488_, v___x_4487_);
return v___x_4489_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4490_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__21, &l_Lean_Parser_withForbiddens___auto__1___closed__21_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__21);
v___x_4491_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__2));
v___x_4492_ = lean_box(2);
v___x_4493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
lean_ctor_set(v___x_4493_, 1, v___x_4491_);
lean_ctor_set(v___x_4493_, 2, v___x_4490_);
return v___x_4493_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1(void){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__22, &l_Lean_Parser_withForbiddens___auto__1___closed__22_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__22);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg___lam__0(lean_object* v_tks_4495_, lean_object* v_c_4496_){
_start:
{
lean_object* v_prec_4497_; lean_object* v_quotDepth_4498_; uint8_t v_suppressInsideQuot_4499_; lean_object* v_savedPos_x3f_4500_; lean_object* v_forbiddenTks_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4515_; 
v_prec_4497_ = lean_ctor_get(v_c_4496_, 0);
v_quotDepth_4498_ = lean_ctor_get(v_c_4496_, 1);
v_suppressInsideQuot_4499_ = lean_ctor_get_uint8(v_c_4496_, sizeof(void*)*4);
v_savedPos_x3f_4500_ = lean_ctor_get(v_c_4496_, 2);
v_forbiddenTks_4501_ = lean_ctor_get(v_c_4496_, 3);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_c_4496_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4503_ = v_c_4496_;
v_isShared_4504_ = v_isSharedCheck_4515_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_forbiddenTks_4501_);
lean_inc(v_savedPos_x3f_4500_);
lean_inc(v_quotDepth_4498_);
lean_inc(v_prec_4497_);
lean_dec(v_c_4496_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4515_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4505_ = lean_array_get_size(v_forbiddenTks_4501_);
v___x_4506_ = lean_unsigned_to_nat(0u);
v___x_4507_ = lean_nat_dec_eq(v___x_4505_, v___x_4506_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4508_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_forbiddenTks_4501_, v_tks_4495_);
lean_dec_ref(v_tks_4495_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 3, v___x_4508_);
v___x_4510_ = v___x_4503_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_prec_4497_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_quotDepth_4498_);
lean_ctor_set(v_reuseFailAlloc_4511_, 2, v_savedPos_x3f_4500_);
lean_ctor_set(v_reuseFailAlloc_4511_, 3, v___x_4508_);
lean_ctor_set_uint8(v_reuseFailAlloc_4511_, sizeof(void*)*4, v_suppressInsideQuot_4499_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
else
{
lean_object* v___x_4513_; 
lean_dec_ref(v_forbiddenTks_4501_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 3, v_tks_4495_);
v___x_4513_ = v___x_4503_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_prec_4497_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_quotDepth_4498_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_savedPos_x3f_4500_);
lean_ctor_set(v_reuseFailAlloc_4514_, 3, v_tks_4495_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*4, v_suppressInsideQuot_4499_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg(lean_object* v_tks_4516_, lean_object* v_p_4517_){
_start:
{
lean_object* v___f_4518_; lean_object* v___x_4519_; 
v___f_4518_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbiddens___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4518_, 0, v_tks_4516_);
v___x_4519_ = l_Lean_Parser_adaptCacheableContext(v___f_4518_, v_p_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens(lean_object* v_tks_4520_, lean_object* v_p_4521_, lean_object* v___h_4522_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_Parser_withForbiddens___redArg(v_tks_4520_, v_p_4521_);
return v___x_4523_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1(){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1));
v___x_4532_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2));
v___x_4533_ = l_Lean_addBuiltinDocString(v___x_4531_, v___x_4532_);
return v___x_4533_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4534_;
v_res_4534_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
stack->m_obj
 = v_res_4534_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___boxed(lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4539_){
_start:
{
lean_object* v_prec_4540_; lean_object* v_quotDepth_4541_; uint8_t v_suppressInsideQuot_4542_; lean_object* v_savedPos_x3f_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4551_; 
v_prec_4540_ = lean_ctor_get(v_x_4539_, 0);
v_quotDepth_4541_ = lean_ctor_get(v_x_4539_, 1);
v_suppressInsideQuot_4542_ = lean_ctor_get_uint8(v_x_4539_, sizeof(void*)*4);
v_savedPos_x3f_4543_ = lean_ctor_get(v_x_4539_, 2);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_x_4539_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v_x_4539_, 3);
lean_dec(v_unused_4552_);
v___x_4545_ = v_x_4539_;
v_isShared_4546_ = v_isSharedCheck_4551_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_savedPos_x3f_4543_);
lean_inc(v_quotDepth_4541_);
lean_inc(v_prec_4540_);
lean_dec(v_x_4539_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4551_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4547_; lean_object* v___x_4549_; 
v___x_4547_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___lam__0___closed__0));
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 3, v___x_4547_);
v___x_4549_ = v___x_4545_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_prec_4540_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_quotDepth_4541_);
lean_ctor_set(v_reuseFailAlloc_4550_, 2, v_savedPos_x3f_4543_);
lean_ctor_set(v_reuseFailAlloc_4550_, 3, v___x_4547_);
lean_ctor_set_uint8(v_reuseFailAlloc_4550_, sizeof(void*)*4, v_suppressInsideQuot_4542_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4554_){
_start:
{
lean_object* v___f_4555_; lean_object* v___x_4556_; 
v___f_4555_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4556_ = l_Lean_Parser_adaptCacheableContext(v___f_4555_, v_p_4554_);
return v___x_4556_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4565_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4566_ = l_Lean_addBuiltinDocString(v___x_4564_, v___x_4565_);
return v___x_4566_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4567_;
v_res_4567_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
stack->m_obj
 = v_res_4567_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4571_, lean_object* v_s_4572_){
_start:
{
lean_object* v_pos_4573_; lean_object* v_toInputContext_4574_; uint8_t v___x_4575_; 
v_pos_4573_ = lean_ctor_get(v_s_4572_, 2);
v_toInputContext_4574_ = lean_ctor_get(v_c_4571_, 0);
v___x_4575_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4574_, v_pos_4573_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4577_ = l_Lean_Parser_ParserState_mkError(v_s_4572_, v___x_4576_);
return v___x_4577_;
}
else
{
return v_s_4572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4578_, lean_object* v_s_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Parser_eoiFn(v_c_4578_, v_s_4579_);
lean_dec_ref(v_c_4578_);
return v_res_4580_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4581_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4582_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
lean_ctor_set(v___x_4583_, 1, v___x_4581_);
return v___x_4583_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4585_, lean_object* v_v_4586_, lean_object* v_t_4587_){
_start:
{
if (lean_obj_tag(v_t_4587_) == 0)
{
lean_object* v_size_4588_; lean_object* v_k_4589_; lean_object* v_v_4590_; lean_object* v_l_4591_; lean_object* v_r_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4872_; 
v_size_4588_ = lean_ctor_get(v_t_4587_, 0);
v_k_4589_ = lean_ctor_get(v_t_4587_, 1);
v_v_4590_ = lean_ctor_get(v_t_4587_, 2);
v_l_4591_ = lean_ctor_get(v_t_4587_, 3);
v_r_4592_ = lean_ctor_get(v_t_4587_, 4);
v_isSharedCheck_4872_ = !lean_is_exclusive(v_t_4587_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4594_ = v_t_4587_;
v_isShared_4595_ = v_isSharedCheck_4872_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_r_4592_);
lean_inc(v_l_4591_);
lean_inc(v_v_4590_);
lean_inc(v_k_4589_);
lean_inc(v_size_4588_);
lean_dec(v_t_4587_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4872_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
uint8_t v___x_4596_; 
v___x_4596_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4585_, v_k_4589_);
switch(v___x_4596_)
{
case 0:
{
lean_object* v_impl_4597_; lean_object* v___x_4598_; 
lean_dec(v_size_4588_);
v_impl_4597_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4585_, v_v_4586_, v_l_4591_);
v___x_4598_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4592_) == 0)
{
lean_object* v_size_4599_; lean_object* v_size_4600_; lean_object* v_k_4601_; lean_object* v_v_4602_; lean_object* v_l_4603_; lean_object* v_r_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; uint8_t v___x_4607_; 
v_size_4599_ = lean_ctor_get(v_r_4592_, 0);
v_size_4600_ = lean_ctor_get(v_impl_4597_, 0);
v_k_4601_ = lean_ctor_get(v_impl_4597_, 1);
v_v_4602_ = lean_ctor_get(v_impl_4597_, 2);
v_l_4603_ = lean_ctor_get(v_impl_4597_, 3);
v_r_4604_ = lean_ctor_get(v_impl_4597_, 4);
lean_inc(v_r_4604_);
v___x_4605_ = lean_unsigned_to_nat(3u);
v___x_4606_ = lean_nat_mul(v___x_4605_, v_size_4599_);
v___x_4607_ = lean_nat_dec_lt(v___x_4606_, v_size_4600_);
lean_dec(v___x_4606_);
if (v___x_4607_ == 0)
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
lean_dec(v_r_4604_);
v___x_4608_ = lean_nat_add(v___x_4598_, v_size_4600_);
v___x_4609_ = lean_nat_add(v___x_4608_, v_size_4599_);
lean_dec(v___x_4608_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 3, v_impl_4597_);
lean_ctor_set(v___x_4594_, 0, v___x_4609_);
v___x_4611_ = v___x_4594_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4612_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4612_, 3, v_impl_4597_);
lean_ctor_set(v_reuseFailAlloc_4612_, 4, v_r_4592_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
else
{
lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4678_; 
lean_inc(v_l_4603_);
lean_inc(v_v_4602_);
lean_inc(v_k_4601_);
lean_inc(v_size_4600_);
v_isSharedCheck_4678_ = !lean_is_exclusive(v_impl_4597_);
if (v_isSharedCheck_4678_ == 0)
{
lean_object* v_unused_4679_; lean_object* v_unused_4680_; lean_object* v_unused_4681_; lean_object* v_unused_4682_; lean_object* v_unused_4683_; 
v_unused_4679_ = lean_ctor_get(v_impl_4597_, 4);
lean_dec(v_unused_4679_);
v_unused_4680_ = lean_ctor_get(v_impl_4597_, 3);
lean_dec(v_unused_4680_);
v_unused_4681_ = lean_ctor_get(v_impl_4597_, 2);
lean_dec(v_unused_4681_);
v_unused_4682_ = lean_ctor_get(v_impl_4597_, 1);
lean_dec(v_unused_4682_);
v_unused_4683_ = lean_ctor_get(v_impl_4597_, 0);
lean_dec(v_unused_4683_);
v___x_4614_ = v_impl_4597_;
v_isShared_4615_ = v_isSharedCheck_4678_;
goto v_resetjp_4613_;
}
else
{
lean_dec(v_impl_4597_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4678_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_size_4616_; lean_object* v_size_4617_; lean_object* v_k_4618_; lean_object* v_v_4619_; lean_object* v_l_4620_; lean_object* v_r_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v_size_4616_ = lean_ctor_get(v_l_4603_, 0);
v_size_4617_ = lean_ctor_get(v_r_4604_, 0);
v_k_4618_ = lean_ctor_get(v_r_4604_, 1);
v_v_4619_ = lean_ctor_get(v_r_4604_, 2);
v_l_4620_ = lean_ctor_get(v_r_4604_, 3);
v_r_4621_ = lean_ctor_get(v_r_4604_, 4);
v___x_4622_ = lean_unsigned_to_nat(2u);
v___x_4623_ = lean_nat_mul(v___x_4622_, v_size_4616_);
v___x_4624_ = lean_nat_dec_lt(v_size_4617_, v___x_4623_);
lean_dec(v___x_4623_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4653_; 
lean_inc(v_r_4621_);
lean_inc(v_l_4620_);
lean_inc(v_v_4619_);
lean_inc(v_k_4618_);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_r_4604_);
if (v_isSharedCheck_4653_ == 0)
{
lean_object* v_unused_4654_; lean_object* v_unused_4655_; lean_object* v_unused_4656_; lean_object* v_unused_4657_; lean_object* v_unused_4658_; 
v_unused_4654_ = lean_ctor_get(v_r_4604_, 4);
lean_dec(v_unused_4654_);
v_unused_4655_ = lean_ctor_get(v_r_4604_, 3);
lean_dec(v_unused_4655_);
v_unused_4656_ = lean_ctor_get(v_r_4604_, 2);
lean_dec(v_unused_4656_);
v_unused_4657_ = lean_ctor_get(v_r_4604_, 1);
lean_dec(v_unused_4657_);
v_unused_4658_ = lean_ctor_get(v_r_4604_, 0);
lean_dec(v_unused_4658_);
v___x_4626_ = v_r_4604_;
v_isShared_4627_ = v_isSharedCheck_4653_;
goto v_resetjp_4625_;
}
else
{
lean_dec(v_r_4604_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4653_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v___x_4641_; lean_object* v___y_4643_; 
v___x_4628_ = lean_nat_add(v___x_4598_, v_size_4600_);
lean_dec(v_size_4600_);
v___x_4629_ = lean_nat_add(v___x_4628_, v_size_4599_);
lean_dec(v___x_4628_);
v___x_4641_ = lean_nat_add(v___x_4598_, v_size_4616_);
if (lean_obj_tag(v_l_4620_) == 0)
{
lean_object* v_size_4651_; 
v_size_4651_ = lean_ctor_get(v_l_4620_, 0);
lean_inc(v_size_4651_);
v___y_4643_ = v_size_4651_;
goto v___jp_4642_;
}
else
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_unsigned_to_nat(0u);
v___y_4643_ = v___x_4652_;
goto v___jp_4642_;
}
v___jp_4630_:
{
lean_object* v___x_4634_; lean_object* v___x_4636_; 
v___x_4634_ = lean_nat_add(v___y_4631_, v___y_4633_);
lean_dec(v___y_4633_);
lean_dec(v___y_4631_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 4, v_r_4592_);
lean_ctor_set(v___x_4626_, 3, v_r_4621_);
lean_ctor_set(v___x_4626_, 2, v_v_4590_);
lean_ctor_set(v___x_4626_, 1, v_k_4589_);
lean_ctor_set(v___x_4626_, 0, v___x_4634_);
v___x_4636_ = v___x_4626_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4640_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4640_, 3, v_r_4621_);
lean_ctor_set(v_reuseFailAlloc_4640_, 4, v_r_4592_);
v___x_4636_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4638_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 4, v___x_4636_);
lean_ctor_set(v___x_4614_, 3, v___y_4632_);
lean_ctor_set(v___x_4614_, 2, v_v_4619_);
lean_ctor_set(v___x_4614_, 1, v_k_4618_);
lean_ctor_set(v___x_4614_, 0, v___x_4629_);
v___x_4638_ = v___x_4614_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_k_4618_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_v_4619_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v___y_4632_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
v___jp_4642_:
{
lean_object* v___x_4644_; lean_object* v___x_4646_; 
v___x_4644_ = lean_nat_add(v___x_4641_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec(v___x_4641_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v_l_4620_);
lean_ctor_set(v___x_4594_, 3, v_l_4603_);
lean_ctor_set(v___x_4594_, 2, v_v_4602_);
lean_ctor_set(v___x_4594_, 1, v_k_4601_);
lean_ctor_set(v___x_4594_, 0, v___x_4644_);
v___x_4646_ = v___x_4594_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_k_4601_);
lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_v_4602_);
lean_ctor_set(v_reuseFailAlloc_4650_, 3, v_l_4603_);
lean_ctor_set(v_reuseFailAlloc_4650_, 4, v_l_4620_);
v___x_4646_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
lean_object* v___x_4647_; 
v___x_4647_ = lean_nat_add(v___x_4598_, v_size_4599_);
if (lean_obj_tag(v_r_4621_) == 0)
{
lean_object* v_size_4648_; 
v_size_4648_ = lean_ctor_get(v_r_4621_, 0);
lean_inc(v_size_4648_);
v___y_4631_ = v___x_4647_;
v___y_4632_ = v___x_4646_;
v___y_4633_ = v_size_4648_;
goto v___jp_4630_;
}
else
{
lean_object* v___x_4649_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v___y_4631_ = v___x_4647_;
v___y_4632_ = v___x_4646_;
v___y_4633_ = v___x_4649_;
goto v___jp_4630_;
}
}
}
}
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
lean_del_object(v___x_4594_);
v___x_4659_ = lean_nat_add(v___x_4598_, v_size_4600_);
lean_dec(v_size_4600_);
v___x_4660_ = lean_nat_add(v___x_4659_, v_size_4599_);
lean_dec(v___x_4659_);
v___x_4661_ = lean_nat_add(v___x_4598_, v_size_4599_);
v___x_4662_ = lean_nat_add(v___x_4661_, v_size_4617_);
lean_dec(v___x_4661_);
lean_inc_ref(v_r_4592_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 4, v_r_4592_);
lean_ctor_set(v___x_4614_, 3, v_r_4604_);
lean_ctor_set(v___x_4614_, 2, v_v_4590_);
lean_ctor_set(v___x_4614_, 1, v_k_4589_);
lean_ctor_set(v___x_4614_, 0, v___x_4662_);
v___x_4664_ = v___x_4614_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4662_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4677_, 3, v_r_4604_);
lean_ctor_set(v_reuseFailAlloc_4677_, 4, v_r_4592_);
v___x_4664_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
v_isSharedCheck_4671_ = !lean_is_exclusive(v_r_4592_);
if (v_isSharedCheck_4671_ == 0)
{
lean_object* v_unused_4672_; lean_object* v_unused_4673_; lean_object* v_unused_4674_; lean_object* v_unused_4675_; lean_object* v_unused_4676_; 
v_unused_4672_ = lean_ctor_get(v_r_4592_, 4);
lean_dec(v_unused_4672_);
v_unused_4673_ = lean_ctor_get(v_r_4592_, 3);
lean_dec(v_unused_4673_);
v_unused_4674_ = lean_ctor_get(v_r_4592_, 2);
lean_dec(v_unused_4674_);
v_unused_4675_ = lean_ctor_get(v_r_4592_, 1);
lean_dec(v_unused_4675_);
v_unused_4676_ = lean_ctor_get(v_r_4592_, 0);
lean_dec(v_unused_4676_);
v___x_4666_ = v_r_4592_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_dec(v_r_4592_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 4, v___x_4664_);
lean_ctor_set(v___x_4666_, 3, v_l_4603_);
lean_ctor_set(v___x_4666_, 2, v_v_4602_);
lean_ctor_set(v___x_4666_, 1, v_k_4601_);
lean_ctor_set(v___x_4666_, 0, v___x_4660_);
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_k_4601_);
lean_ctor_set(v_reuseFailAlloc_4670_, 2, v_v_4602_);
lean_ctor_set(v_reuseFailAlloc_4670_, 3, v_l_4603_);
lean_ctor_set(v_reuseFailAlloc_4670_, 4, v___x_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4684_; 
v_l_4684_ = lean_ctor_get(v_impl_4597_, 3);
if (lean_obj_tag(v_l_4684_) == 0)
{
lean_object* v_r_4685_; lean_object* v_k_4686_; lean_object* v_v_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4698_; 
lean_inc_ref(v_l_4684_);
v_r_4685_ = lean_ctor_get(v_impl_4597_, 4);
v_k_4686_ = lean_ctor_get(v_impl_4597_, 1);
v_v_4687_ = lean_ctor_get(v_impl_4597_, 2);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_impl_4597_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; lean_object* v_unused_4700_; 
v_unused_4699_ = lean_ctor_get(v_impl_4597_, 3);
lean_dec(v_unused_4699_);
v_unused_4700_ = lean_ctor_get(v_impl_4597_, 0);
lean_dec(v_unused_4700_);
v___x_4689_ = v_impl_4597_;
v_isShared_4690_ = v_isSharedCheck_4698_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_r_4685_);
lean_inc(v_v_4687_);
lean_inc(v_k_4686_);
lean_dec(v_impl_4597_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4698_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4693_; 
v___x_4691_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4685_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 3, v_r_4685_);
lean_ctor_set(v___x_4689_, 2, v_v_4590_);
lean_ctor_set(v___x_4689_, 1, v_k_4589_);
lean_ctor_set(v___x_4689_, 0, v___x_4598_);
v___x_4693_ = v___x_4689_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_r_4685_);
lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_r_4685_);
v___x_4693_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
lean_object* v___x_4695_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v___x_4693_);
lean_ctor_set(v___x_4594_, 3, v_l_4684_);
lean_ctor_set(v___x_4594_, 2, v_v_4687_);
lean_ctor_set(v___x_4594_, 1, v_k_4686_);
lean_ctor_set(v___x_4594_, 0, v___x_4691_);
v___x_4695_ = v___x_4594_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4691_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_k_4686_);
lean_ctor_set(v_reuseFailAlloc_4696_, 2, v_v_4687_);
lean_ctor_set(v_reuseFailAlloc_4696_, 3, v_l_4684_);
lean_ctor_set(v_reuseFailAlloc_4696_, 4, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
else
{
lean_object* v_r_4701_; 
v_r_4701_ = lean_ctor_get(v_impl_4597_, 4);
lean_inc(v_r_4701_);
if (lean_obj_tag(v_r_4701_) == 0)
{
lean_object* v_k_4702_; lean_object* v_v_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4726_; 
lean_inc(v_l_4684_);
v_k_4702_ = lean_ctor_get(v_impl_4597_, 1);
v_v_4703_ = lean_ctor_get(v_impl_4597_, 2);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_impl_4597_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; 
v_unused_4727_ = lean_ctor_get(v_impl_4597_, 4);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_impl_4597_, 3);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_impl_4597_, 0);
lean_dec(v_unused_4729_);
v___x_4705_ = v_impl_4597_;
v_isShared_4706_ = v_isSharedCheck_4726_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_v_4703_);
lean_inc(v_k_4702_);
lean_dec(v_impl_4597_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4726_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v_k_4707_; lean_object* v_v_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4722_; 
v_k_4707_ = lean_ctor_get(v_r_4701_, 1);
v_v_4708_ = lean_ctor_get(v_r_4701_, 2);
v_isSharedCheck_4722_ = !lean_is_exclusive(v_r_4701_);
if (v_isSharedCheck_4722_ == 0)
{
lean_object* v_unused_4723_; lean_object* v_unused_4724_; lean_object* v_unused_4725_; 
v_unused_4723_ = lean_ctor_get(v_r_4701_, 4);
lean_dec(v_unused_4723_);
v_unused_4724_ = lean_ctor_get(v_r_4701_, 3);
lean_dec(v_unused_4724_);
v_unused_4725_ = lean_ctor_get(v_r_4701_, 0);
lean_dec(v_unused_4725_);
v___x_4710_ = v_r_4701_;
v_isShared_4711_ = v_isSharedCheck_4722_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_v_4708_);
lean_inc(v_k_4707_);
lean_dec(v_r_4701_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4722_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4712_; lean_object* v___x_4714_; 
v___x_4712_ = lean_unsigned_to_nat(3u);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 4, v_l_4684_);
lean_ctor_set(v___x_4710_, 3, v_l_4684_);
lean_ctor_set(v___x_4710_, 2, v_v_4703_);
lean_ctor_set(v___x_4710_, 1, v_k_4702_);
lean_ctor_set(v___x_4710_, 0, v___x_4598_);
v___x_4714_ = v___x_4710_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v_k_4702_);
lean_ctor_set(v_reuseFailAlloc_4721_, 2, v_v_4703_);
lean_ctor_set(v_reuseFailAlloc_4721_, 3, v_l_4684_);
lean_ctor_set(v_reuseFailAlloc_4721_, 4, v_l_4684_);
v___x_4714_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4716_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 4, v_l_4684_);
lean_ctor_set(v___x_4705_, 2, v_v_4590_);
lean_ctor_set(v___x_4705_, 1, v_k_4589_);
lean_ctor_set(v___x_4705_, 0, v___x_4598_);
v___x_4716_ = v___x_4705_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4720_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4720_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4720_, 3, v_l_4684_);
lean_ctor_set(v_reuseFailAlloc_4720_, 4, v_l_4684_);
v___x_4716_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4718_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v___x_4716_);
lean_ctor_set(v___x_4594_, 3, v___x_4714_);
lean_ctor_set(v___x_4594_, 2, v_v_4708_);
lean_ctor_set(v___x_4594_, 1, v_k_4707_);
lean_ctor_set(v___x_4594_, 0, v___x_4712_);
v___x_4718_ = v___x_4594_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_k_4707_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_v_4708_);
lean_ctor_set(v_reuseFailAlloc_4719_, 3, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4719_, 4, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4732_; 
v___x_4730_ = lean_unsigned_to_nat(2u);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v_r_4701_);
lean_ctor_set(v___x_4594_, 3, v_impl_4597_);
lean_ctor_set(v___x_4594_, 0, v___x_4730_);
v___x_4732_ = v___x_4594_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4733_, 3, v_impl_4597_);
lean_ctor_set(v_reuseFailAlloc_4733_, 4, v_r_4701_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4735_; 
lean_dec(v_v_4590_);
lean_dec(v_k_4589_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 2, v_v_4586_);
lean_ctor_set(v___x_4594_, 1, v_k_4585_);
v___x_4735_ = v___x_4594_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_size_4588_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v_k_4585_);
lean_ctor_set(v_reuseFailAlloc_4736_, 2, v_v_4586_);
lean_ctor_set(v_reuseFailAlloc_4736_, 3, v_l_4591_);
lean_ctor_set(v_reuseFailAlloc_4736_, 4, v_r_4592_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
default: 
{
lean_object* v_impl_4737_; lean_object* v___x_4738_; 
lean_dec(v_size_4588_);
v_impl_4737_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4585_, v_v_4586_, v_r_4592_);
v___x_4738_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4591_) == 0)
{
lean_object* v_size_4739_; lean_object* v_size_4740_; lean_object* v_k_4741_; lean_object* v_v_4742_; lean_object* v_l_4743_; lean_object* v_r_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v_size_4739_ = lean_ctor_get(v_l_4591_, 0);
v_size_4740_ = lean_ctor_get(v_impl_4737_, 0);
v_k_4741_ = lean_ctor_get(v_impl_4737_, 1);
v_v_4742_ = lean_ctor_get(v_impl_4737_, 2);
v_l_4743_ = lean_ctor_get(v_impl_4737_, 3);
lean_inc(v_l_4743_);
v_r_4744_ = lean_ctor_get(v_impl_4737_, 4);
v___x_4745_ = lean_unsigned_to_nat(3u);
v___x_4746_ = lean_nat_mul(v___x_4745_, v_size_4739_);
v___x_4747_ = lean_nat_dec_lt(v___x_4746_, v_size_4740_);
lean_dec(v___x_4746_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4751_; 
lean_dec(v_l_4743_);
v___x_4748_ = lean_nat_add(v___x_4738_, v_size_4739_);
v___x_4749_ = lean_nat_add(v___x_4748_, v_size_4740_);
lean_dec(v___x_4748_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v_impl_4737_);
lean_ctor_set(v___x_4594_, 0, v___x_4749_);
v___x_4751_ = v___x_4594_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4752_, 3, v_l_4591_);
lean_ctor_set(v_reuseFailAlloc_4752_, 4, v_impl_4737_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
else
{
lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4816_; 
lean_inc(v_r_4744_);
lean_inc(v_v_4742_);
lean_inc(v_k_4741_);
lean_inc(v_size_4740_);
v_isSharedCheck_4816_ = !lean_is_exclusive(v_impl_4737_);
if (v_isSharedCheck_4816_ == 0)
{
lean_object* v_unused_4817_; lean_object* v_unused_4818_; lean_object* v_unused_4819_; lean_object* v_unused_4820_; lean_object* v_unused_4821_; 
v_unused_4817_ = lean_ctor_get(v_impl_4737_, 4);
lean_dec(v_unused_4817_);
v_unused_4818_ = lean_ctor_get(v_impl_4737_, 3);
lean_dec(v_unused_4818_);
v_unused_4819_ = lean_ctor_get(v_impl_4737_, 2);
lean_dec(v_unused_4819_);
v_unused_4820_ = lean_ctor_get(v_impl_4737_, 1);
lean_dec(v_unused_4820_);
v_unused_4821_ = lean_ctor_get(v_impl_4737_, 0);
lean_dec(v_unused_4821_);
v___x_4754_ = v_impl_4737_;
v_isShared_4755_ = v_isSharedCheck_4816_;
goto v_resetjp_4753_;
}
else
{
lean_dec(v_impl_4737_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4816_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v_size_4756_; lean_object* v_k_4757_; lean_object* v_v_4758_; lean_object* v_l_4759_; lean_object* v_r_4760_; lean_object* v_size_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v_size_4756_ = lean_ctor_get(v_l_4743_, 0);
v_k_4757_ = lean_ctor_get(v_l_4743_, 1);
v_v_4758_ = lean_ctor_get(v_l_4743_, 2);
v_l_4759_ = lean_ctor_get(v_l_4743_, 3);
v_r_4760_ = lean_ctor_get(v_l_4743_, 4);
v_size_4761_ = lean_ctor_get(v_r_4744_, 0);
v___x_4762_ = lean_unsigned_to_nat(2u);
v___x_4763_ = lean_nat_mul(v___x_4762_, v_size_4761_);
v___x_4764_ = lean_nat_dec_lt(v_size_4756_, v___x_4763_);
lean_dec(v___x_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4792_; 
lean_inc(v_r_4760_);
lean_inc(v_l_4759_);
lean_inc(v_v_4758_);
lean_inc(v_k_4757_);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_l_4743_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; lean_object* v_unused_4794_; lean_object* v_unused_4795_; lean_object* v_unused_4796_; lean_object* v_unused_4797_; 
v_unused_4793_ = lean_ctor_get(v_l_4743_, 4);
lean_dec(v_unused_4793_);
v_unused_4794_ = lean_ctor_get(v_l_4743_, 3);
lean_dec(v_unused_4794_);
v_unused_4795_ = lean_ctor_get(v_l_4743_, 2);
lean_dec(v_unused_4795_);
v_unused_4796_ = lean_ctor_get(v_l_4743_, 1);
lean_dec(v_unused_4796_);
v_unused_4797_ = lean_ctor_get(v_l_4743_, 0);
lean_dec(v_unused_4797_);
v___x_4766_ = v_l_4743_;
v_isShared_4767_ = v_isSharedCheck_4792_;
goto v_resetjp_4765_;
}
else
{
lean_dec(v_l_4743_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4792_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v___y_4773_; lean_object* v___y_4782_; 
v___x_4768_ = lean_nat_add(v___x_4738_, v_size_4739_);
v___x_4769_ = lean_nat_add(v___x_4768_, v_size_4740_);
lean_dec(v_size_4740_);
if (lean_obj_tag(v_l_4759_) == 0)
{
lean_object* v_size_4790_; 
v_size_4790_ = lean_ctor_get(v_l_4759_, 0);
lean_inc(v_size_4790_);
v___y_4782_ = v_size_4790_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4791_; 
v___x_4791_ = lean_unsigned_to_nat(0u);
v___y_4782_ = v___x_4791_;
goto v___jp_4781_;
}
v___jp_4770_:
{
lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4774_ = lean_nat_add(v___y_4771_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec(v___y_4771_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 4, v_r_4744_);
lean_ctor_set(v___x_4766_, 3, v_r_4760_);
lean_ctor_set(v___x_4766_, 2, v_v_4742_);
lean_ctor_set(v___x_4766_, 1, v_k_4741_);
lean_ctor_set(v___x_4766_, 0, v___x_4774_);
v___x_4776_ = v___x_4766_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4774_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_k_4741_);
lean_ctor_set(v_reuseFailAlloc_4780_, 2, v_v_4742_);
lean_ctor_set(v_reuseFailAlloc_4780_, 3, v_r_4760_);
lean_ctor_set(v_reuseFailAlloc_4780_, 4, v_r_4744_);
v___x_4776_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
lean_object* v___x_4778_; 
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 4, v___x_4776_);
lean_ctor_set(v___x_4754_, 3, v___y_4772_);
lean_ctor_set(v___x_4754_, 2, v_v_4758_);
lean_ctor_set(v___x_4754_, 1, v_k_4757_);
lean_ctor_set(v___x_4754_, 0, v___x_4769_);
v___x_4778_ = v___x_4754_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4769_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v_k_4757_);
lean_ctor_set(v_reuseFailAlloc_4779_, 2, v_v_4758_);
lean_ctor_set(v_reuseFailAlloc_4779_, 3, v___y_4772_);
lean_ctor_set(v_reuseFailAlloc_4779_, 4, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
v___jp_4781_:
{
lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4783_ = lean_nat_add(v___x_4768_, v___y_4782_);
lean_dec(v___y_4782_);
lean_dec(v___x_4768_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v_l_4759_);
lean_ctor_set(v___x_4594_, 0, v___x_4783_);
v___x_4785_ = v___x_4594_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_l_4591_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_l_4759_);
v___x_4785_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_nat_add(v___x_4738_, v_size_4761_);
if (lean_obj_tag(v_r_4760_) == 0)
{
lean_object* v_size_4787_; 
v_size_4787_ = lean_ctor_get(v_r_4760_, 0);
lean_inc(v_size_4787_);
v___y_4771_ = v___x_4786_;
v___y_4772_ = v___x_4785_;
v___y_4773_ = v_size_4787_;
goto v___jp_4770_;
}
else
{
lean_object* v___x_4788_; 
v___x_4788_ = lean_unsigned_to_nat(0u);
v___y_4771_ = v___x_4786_;
v___y_4772_ = v___x_4785_;
v___y_4773_ = v___x_4788_;
goto v___jp_4770_;
}
}
}
}
}
else
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
lean_del_object(v___x_4594_);
v___x_4798_ = lean_nat_add(v___x_4738_, v_size_4739_);
v___x_4799_ = lean_nat_add(v___x_4798_, v_size_4740_);
lean_dec(v_size_4740_);
v___x_4800_ = lean_nat_add(v___x_4798_, v_size_4756_);
lean_dec(v___x_4798_);
lean_inc_ref(v_l_4591_);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 4, v_l_4743_);
lean_ctor_set(v___x_4754_, 3, v_l_4591_);
lean_ctor_set(v___x_4754_, 2, v_v_4590_);
lean_ctor_set(v___x_4754_, 1, v_k_4589_);
lean_ctor_set(v___x_4754_, 0, v___x_4800_);
v___x_4802_ = v___x_4754_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v_l_4591_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_l_4743_);
v___x_4802_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
v_isSharedCheck_4809_ = !lean_is_exclusive(v_l_4591_);
if (v_isSharedCheck_4809_ == 0)
{
lean_object* v_unused_4810_; lean_object* v_unused_4811_; lean_object* v_unused_4812_; lean_object* v_unused_4813_; lean_object* v_unused_4814_; 
v_unused_4810_ = lean_ctor_get(v_l_4591_, 4);
lean_dec(v_unused_4810_);
v_unused_4811_ = lean_ctor_get(v_l_4591_, 3);
lean_dec(v_unused_4811_);
v_unused_4812_ = lean_ctor_get(v_l_4591_, 2);
lean_dec(v_unused_4812_);
v_unused_4813_ = lean_ctor_get(v_l_4591_, 1);
lean_dec(v_unused_4813_);
v_unused_4814_ = lean_ctor_get(v_l_4591_, 0);
lean_dec(v_unused_4814_);
v___x_4804_ = v_l_4591_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_dec(v_l_4591_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 4, v_r_4744_);
lean_ctor_set(v___x_4804_, 3, v___x_4802_);
lean_ctor_set(v___x_4804_, 2, v_v_4742_);
lean_ctor_set(v___x_4804_, 1, v_k_4741_);
lean_ctor_set(v___x_4804_, 0, v___x_4799_);
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v_k_4741_);
lean_ctor_set(v_reuseFailAlloc_4808_, 2, v_v_4742_);
lean_ctor_set(v_reuseFailAlloc_4808_, 3, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4808_, 4, v_r_4744_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4822_; 
v_l_4822_ = lean_ctor_get(v_impl_4737_, 3);
lean_inc(v_l_4822_);
if (lean_obj_tag(v_l_4822_) == 0)
{
lean_object* v_r_4823_; lean_object* v_k_4824_; lean_object* v_v_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4848_; 
v_r_4823_ = lean_ctor_get(v_impl_4737_, 4);
v_k_4824_ = lean_ctor_get(v_impl_4737_, 1);
v_v_4825_ = lean_ctor_get(v_impl_4737_, 2);
v_isSharedCheck_4848_ = !lean_is_exclusive(v_impl_4737_);
if (v_isSharedCheck_4848_ == 0)
{
lean_object* v_unused_4849_; lean_object* v_unused_4850_; 
v_unused_4849_ = lean_ctor_get(v_impl_4737_, 3);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_impl_4737_, 0);
lean_dec(v_unused_4850_);
v___x_4827_ = v_impl_4737_;
v_isShared_4828_ = v_isSharedCheck_4848_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_r_4823_);
lean_inc(v_v_4825_);
lean_inc(v_k_4824_);
lean_dec(v_impl_4737_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4848_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v_k_4829_; lean_object* v_v_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4844_; 
v_k_4829_ = lean_ctor_get(v_l_4822_, 1);
v_v_4830_ = lean_ctor_get(v_l_4822_, 2);
v_isSharedCheck_4844_ = !lean_is_exclusive(v_l_4822_);
if (v_isSharedCheck_4844_ == 0)
{
lean_object* v_unused_4845_; lean_object* v_unused_4846_; lean_object* v_unused_4847_; 
v_unused_4845_ = lean_ctor_get(v_l_4822_, 4);
lean_dec(v_unused_4845_);
v_unused_4846_ = lean_ctor_get(v_l_4822_, 3);
lean_dec(v_unused_4846_);
v_unused_4847_ = lean_ctor_get(v_l_4822_, 0);
lean_dec(v_unused_4847_);
v___x_4832_ = v_l_4822_;
v_isShared_4833_ = v_isSharedCheck_4844_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_v_4830_);
lean_inc(v_k_4829_);
lean_dec(v_l_4822_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4844_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4834_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4823_, 2);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 4, v_r_4823_);
lean_ctor_set(v___x_4832_, 3, v_r_4823_);
lean_ctor_set(v___x_4832_, 2, v_v_4590_);
lean_ctor_set(v___x_4832_, 1, v_k_4589_);
lean_ctor_set(v___x_4832_, 0, v___x_4738_);
v___x_4836_ = v___x_4832_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4843_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4843_, 3, v_r_4823_);
lean_ctor_set(v_reuseFailAlloc_4843_, 4, v_r_4823_);
v___x_4836_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
lean_object* v___x_4838_; 
lean_inc(v_r_4823_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 3, v_r_4823_);
lean_ctor_set(v___x_4827_, 0, v___x_4738_);
v___x_4838_ = v___x_4827_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v_k_4824_);
lean_ctor_set(v_reuseFailAlloc_4842_, 2, v_v_4825_);
lean_ctor_set(v_reuseFailAlloc_4842_, 3, v_r_4823_);
lean_ctor_set(v_reuseFailAlloc_4842_, 4, v_r_4823_);
v___x_4838_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4840_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v___x_4838_);
lean_ctor_set(v___x_4594_, 3, v___x_4836_);
lean_ctor_set(v___x_4594_, 2, v_v_4830_);
lean_ctor_set(v___x_4594_, 1, v_k_4829_);
lean_ctor_set(v___x_4594_, 0, v___x_4834_);
v___x_4840_ = v___x_4594_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4834_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_k_4829_);
lean_ctor_set(v_reuseFailAlloc_4841_, 2, v_v_4830_);
lean_ctor_set(v_reuseFailAlloc_4841_, 3, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4841_, 4, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
}
else
{
lean_object* v_r_4851_; 
v_r_4851_ = lean_ctor_get(v_impl_4737_, 4);
lean_inc(v_r_4851_);
if (lean_obj_tag(v_r_4851_) == 0)
{
lean_object* v_k_4852_; lean_object* v_v_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4864_; 
v_k_4852_ = lean_ctor_get(v_impl_4737_, 1);
v_v_4853_ = lean_ctor_get(v_impl_4737_, 2);
v_isSharedCheck_4864_ = !lean_is_exclusive(v_impl_4737_);
if (v_isSharedCheck_4864_ == 0)
{
lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; 
v_unused_4865_ = lean_ctor_get(v_impl_4737_, 4);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_impl_4737_, 3);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_impl_4737_, 0);
lean_dec(v_unused_4867_);
v___x_4855_ = v_impl_4737_;
v_isShared_4856_ = v_isSharedCheck_4864_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_v_4853_);
lean_inc(v_k_4852_);
lean_dec(v_impl_4737_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4864_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4857_; lean_object* v___x_4859_; 
v___x_4857_ = lean_unsigned_to_nat(3u);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 4, v_l_4822_);
lean_ctor_set(v___x_4855_, 2, v_v_4590_);
lean_ctor_set(v___x_4855_, 1, v_k_4589_);
lean_ctor_set(v___x_4855_, 0, v___x_4738_);
v___x_4859_ = v___x_4855_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4863_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4863_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4863_, 3, v_l_4822_);
lean_ctor_set(v_reuseFailAlloc_4863_, 4, v_l_4822_);
v___x_4859_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
lean_object* v___x_4861_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v_r_4851_);
lean_ctor_set(v___x_4594_, 3, v___x_4859_);
lean_ctor_set(v___x_4594_, 2, v_v_4853_);
lean_ctor_set(v___x_4594_, 1, v_k_4852_);
lean_ctor_set(v___x_4594_, 0, v___x_4857_);
v___x_4861_ = v___x_4594_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4857_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_k_4852_);
lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_v_4853_);
lean_ctor_set(v_reuseFailAlloc_4862_, 3, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4862_, 4, v_r_4851_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_object* v___x_4868_; lean_object* v___x_4870_; 
v___x_4868_ = lean_unsigned_to_nat(2u);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 4, v_impl_4737_);
lean_ctor_set(v___x_4594_, 3, v_r_4851_);
lean_ctor_set(v___x_4594_, 0, v___x_4868_);
v___x_4870_ = v___x_4594_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4868_);
lean_ctor_set(v_reuseFailAlloc_4871_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4871_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4871_, 3, v_r_4851_);
lean_ctor_set(v_reuseFailAlloc_4871_, 4, v_impl_4737_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
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
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_unsigned_to_nat(1u);
v___x_4874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
lean_ctor_set(v___x_4874_, 1, v_k_4585_);
lean_ctor_set(v___x_4874_, 2, v_v_4586_);
lean_ctor_set(v___x_4874_, 3, v_t_4587_);
lean_ctor_set(v___x_4874_, 4, v_t_4587_);
return v___x_4874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4875_, lean_object* v_k_4876_){
_start:
{
if (lean_obj_tag(v_t_4875_) == 0)
{
lean_object* v_k_4877_; lean_object* v_v_4878_; lean_object* v_l_4879_; lean_object* v_r_4880_; uint8_t v___x_4881_; 
v_k_4877_ = lean_ctor_get(v_t_4875_, 1);
v_v_4878_ = lean_ctor_get(v_t_4875_, 2);
v_l_4879_ = lean_ctor_get(v_t_4875_, 3);
v_r_4880_ = lean_ctor_get(v_t_4875_, 4);
v___x_4881_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4876_, v_k_4877_);
switch(v___x_4881_)
{
case 0:
{
v_t_4875_ = v_l_4879_;
goto _start;
}
case 1:
{
lean_object* v___x_4883_; 
lean_inc(v_v_4878_);
v___x_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4883_, 0, v_v_4878_);
return v___x_4883_;
}
default: 
{
v_t_4875_ = v_r_4880_;
goto _start;
}
}
}
else
{
lean_object* v___x_4885_; 
v___x_4885_ = lean_box(0);
return v___x_4885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4886_, lean_object* v_k_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4886_, v_k_4887_);
lean_dec(v_k_4887_);
lean_dec(v_t_4886_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4889_, lean_object* v_k_4890_, lean_object* v_v_4891_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4889_, v_k_4890_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = lean_box(0);
v___x_4894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4894_, 0, v_v_4891_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4890_, v___x_4894_, v_map_4889_);
return v___x_4895_;
}
else
{
lean_object* v_val_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v_val_4896_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_val_4896_);
lean_dec_ref_known(v___x_4892_, 1);
v___x_4897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4897_, 0, v_v_4891_);
lean_ctor_set(v___x_4897_, 1, v_val_4896_);
v___x_4898_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4890_, v___x_4897_, v_map_4889_);
return v___x_4898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4899_, lean_object* v_map_4900_, lean_object* v_k_4901_, lean_object* v_v_4902_){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4900_, v_k_4901_, v_v_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4904_, lean_object* v_t_4905_, lean_object* v_k_4906_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4905_, v_k_4906_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4908_, lean_object* v_t_4909_, lean_object* v_k_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4908_, v_t_4909_, v_k_4910_);
lean_dec(v_k_4910_);
lean_dec(v_t_4909_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4912_, lean_object* v_k_4913_, lean_object* v_v_4914_, lean_object* v_t_4915_, lean_object* v_hl_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4913_, v_v_4914_, v_t_4915_);
return v___x_4917_;
}
}
lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = lean_box(1);
return v___x_4919_;
}
}
LEAN_EXPORT void l_Lean_Parser_TokenMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4920_;
v_res_4920_ = l_Lean_Parser_TokenMap_instInhabited___redArg();
stack->m_obj
 = v_res_4920_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg___boxed(lean_object* v___dummy_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Parser_TokenMap_instInhabited___redArg();
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4923_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_box(1);
return v___x_4924_;
}
}
lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_box(1);
return v___x_4926_;
}
}
LEAN_EXPORT void l_Lean_Parser_TokenMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4927_;
v_res_4927_ = l_Lean_Parser_TokenMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_4927_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Parser_TokenMap_instEmptyCollection___redArg();
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4930_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = lean_box(1);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4932_, lean_object* v_a_4933_, lean_object* v_b_4934_, lean_object* v_c_4935_){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4936_, 0, v_a_4933_);
lean_ctor_set(v___x_4936_, 1, v_b_4934_);
v___x_4937_ = lean_apply_2(v_f_4932_, v___x_4936_, v_c_4935_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4938_, lean_object* v_____do__lift_4939_){
_start:
{
lean_object* v_a_4940_; lean_object* v___x_4941_; 
v_a_4940_ = lean_ctor_get(v_____do__lift_4939_, 0);
lean_inc(v_a_4940_);
lean_dec_ref(v_____do__lift_4939_);
v___x_4941_ = lean_apply_2(v_toPure_4938_, lean_box(0), v_a_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4942_, lean_object* v_m_4943_, lean_object* v_init_4944_, lean_object* v_f_4945_){
_start:
{
lean_object* v_toApplicative_4946_; lean_object* v_toBind_4947_; lean_object* v_toPure_4948_; lean_object* v___f_4949_; lean_object* v___x_4950_; lean_object* v___f_4951_; lean_object* v___x_4952_; 
v_toApplicative_4946_ = lean_ctor_get(v_inst_4942_, 0);
v_toBind_4947_ = lean_ctor_get(v_inst_4942_, 1);
lean_inc(v_toBind_4947_);
v_toPure_4948_ = lean_ctor_get(v_toApplicative_4946_, 1);
lean_inc(v_toPure_4948_);
v___f_4949_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4949_, 0, v_f_4945_);
v___x_4950_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4942_, v___f_4949_, v_init_4944_, v_m_4943_);
v___f_4951_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4951_, 0, v_toPure_4948_);
v___x_4952_ = lean_apply_4(v_toBind_4947_, lean_box(0), lean_box(0), v___x_4950_, v___f_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4953_, lean_object* v_00_u03b1_4954_, lean_object* v_inst_4955_, lean_object* v_00_u03b2_4956_, lean_object* v_m_4957_, lean_object* v_init_4958_, lean_object* v_f_4959_){
_start:
{
lean_object* v_toApplicative_4960_; lean_object* v_toBind_4961_; lean_object* v_toPure_4962_; lean_object* v___f_4963_; lean_object* v___x_4964_; lean_object* v___f_4965_; lean_object* v___x_4966_; 
v_toApplicative_4960_ = lean_ctor_get(v_inst_4955_, 0);
v_toBind_4961_ = lean_ctor_get(v_inst_4955_, 1);
lean_inc(v_toBind_4961_);
v_toPure_4962_ = lean_ctor_get(v_toApplicative_4960_, 1);
lean_inc(v_toPure_4962_);
v___f_4963_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4963_, 0, v_f_4959_);
v___x_4964_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4955_, v___f_4963_, v_init_4958_, v_m_4957_);
v___f_4965_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4965_, 0, v_toPure_4962_);
v___x_4966_ = lean_apply_4(v_toBind_4961_, lean_box(0), lean_box(0), v___x_4964_, v___f_4965_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4967_){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4968_, 0, lean_box(0));
lean_closure_set(v___x_4968_, 1, lean_box(0));
lean_closure_set(v___x_4968_, 2, v_inst_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4969_, lean_object* v_00_u03b1_4970_, lean_object* v_inst_4971_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4972_, 0, lean_box(0));
lean_closure_set(v___x_4972_, 1, lean_box(0));
lean_closure_set(v___x_4972_, 2, v_inst_4971_);
return v___x_4972_;
}
}
lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(uint8_t v_x_4977_){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = lean_box(v_x_4977_);
v___x_4979_ = lean_obj_tag_nat(v___x_4978_);
lean_dec(v___x_4978_);
return v___x_4979_;
}
}
LEAN_EXPORT void l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4977_ = stack[0].m_num;
lean_object* v_res_4980_;
v_res_4980_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(v_x_4977_);
stack->m_obj
 = v_res_4980_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl___boxed(lean_object* v_x_4981_){
_start:
{
uint8_t v_x_4__boxed_4982_; lean_object* v_res_4983_; 
v_x_4__boxed_4982_ = lean_unbox(v_x_4981_);
v_res_4983_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(v_x_4__boxed_4982_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4984_){
_start:
{
lean_inc(v_k_4984_);
return v_k_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4985_);
lean_dec(v_k_4985_);
return v_res_4986_;
}
}
lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4987_, lean_object* v_ctorIdx_4988_, uint8_t v_t_4989_, lean_object* v_h_4990_, lean_object* v_k_4991_){
_start:
{
lean_inc(v_k_4991_);
return v_k_4991_;
}
}
LEAN_EXPORT void l_Lean_Parser_LeadingIdentBehavior_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_4988_ = stack[1].m_obj;
uint8_t v_t_4989_ = stack[2].m_num;
lean_object* v_k_4991_ = stack[4].m_obj;
lean_object* v_res_4992_;
v_res_4992_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_box(0), v_ctorIdx_4988_, v_t_4989_, lean_box(0), v_k_4991_);
stack->m_obj
 = v_res_4992_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4993_, lean_object* v_ctorIdx_4994_, lean_object* v_t_4995_, lean_object* v_h_4996_, lean_object* v_k_4997_){
_start:
{
uint8_t v_t_boxed_4998_; lean_object* v_res_4999_; 
v_t_boxed_4998_ = lean_unbox(v_t_4995_);
v_res_4999_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4993_, v_ctorIdx_4994_, v_t_boxed_4998_, v_h_4996_, v_k_4997_);
lean_dec(v_k_4997_);
lean_dec(v_ctorIdx_4994_);
return v_res_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_5000_){
_start:
{
lean_inc(v_default_5000_);
return v_default_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_5001_);
lean_dec(v_default_5001_);
return v_res_5002_;
}
}
lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_5003_, uint8_t v_t_5004_, lean_object* v_h_5005_, lean_object* v_default_5006_){
_start:
{
lean_inc(v_default_5006_);
return v_default_5006_;
}
}
LEAN_EXPORT void l_Lean_Parser_LeadingIdentBehavior_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_5004_ = stack[1].m_num;
lean_object* v_default_5006_ = stack[3].m_obj;
lean_object* v_res_5007_;
v_res_5007_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_box(0), v_t_5004_, lean_box(0), v_default_5006_);
stack->m_obj
 = v_res_5007_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_5008_, lean_object* v_t_5009_, lean_object* v_h_5010_, lean_object* v_default_5011_){
_start:
{
uint8_t v_t_boxed_5012_; lean_object* v_res_5013_; 
v_t_boxed_5012_ = lean_unbox(v_t_5009_);
v_res_5013_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_5008_, v_t_boxed_5012_, v_h_5010_, v_default_5011_);
lean_dec(v_default_5011_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_5014_){
_start:
{
lean_inc(v_symbol_5014_);
return v_symbol_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_5015_);
lean_dec(v_symbol_5015_);
return v_res_5016_;
}
}
lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_5017_, uint8_t v_t_5018_, lean_object* v_h_5019_, lean_object* v_symbol_5020_){
_start:
{
lean_inc(v_symbol_5020_);
return v_symbol_5020_;
}
}
LEAN_EXPORT void l_Lean_Parser_LeadingIdentBehavior_symbol_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_5018_ = stack[1].m_num;
lean_object* v_symbol_5020_ = stack[3].m_obj;
lean_object* v_res_5021_;
v_res_5021_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_box(0), v_t_5018_, lean_box(0), v_symbol_5020_);
stack->m_obj
 = v_res_5021_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_5022_, lean_object* v_t_5023_, lean_object* v_h_5024_, lean_object* v_symbol_5025_){
_start:
{
uint8_t v_t_boxed_5026_; lean_object* v_res_5027_; 
v_t_boxed_5026_ = lean_unbox(v_t_5023_);
v_res_5027_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_5022_, v_t_boxed_5026_, v_h_5024_, v_symbol_5025_);
lean_dec(v_symbol_5025_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_5028_){
_start:
{
lean_inc(v_both_5028_);
return v_both_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_5029_);
lean_dec(v_both_5029_);
return v_res_5030_;
}
}
lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_5031_, uint8_t v_t_5032_, lean_object* v_h_5033_, lean_object* v_both_5034_){
_start:
{
lean_inc(v_both_5034_);
return v_both_5034_;
}
}
LEAN_EXPORT void l_Lean_Parser_LeadingIdentBehavior_both_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_5032_ = stack[1].m_num;
lean_object* v_both_5034_ = stack[3].m_obj;
lean_object* v_res_5035_;
v_res_5035_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_box(0), v_t_5032_, lean_box(0), v_both_5034_);
stack->m_obj
 = v_res_5035_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_5036_, lean_object* v_t_5037_, lean_object* v_h_5038_, lean_object* v_both_5039_){
_start:
{
uint8_t v_t_boxed_5040_; lean_object* v_res_5041_; 
v_t_boxed_5040_ = lean_unbox(v_t_5037_);
v_res_5041_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_5036_, v_t_boxed_5040_, v_h_5038_, v_both_5039_);
lean_dec(v_both_5039_);
return v_res_5041_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_5042_; 
v___x_5042_ = 0;
return v___x_5042_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_5043_; 
v___x_5043_ = 0;
return v___x_5043_;
}
}
uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_5044_, uint8_t v_y_5045_){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; uint8_t v___x_5050_; 
v___x_5046_ = lean_box(v_x_5044_);
v___x_5047_ = lean_obj_tag_nat(v___x_5046_);
lean_dec(v___x_5046_);
v___x_5048_ = lean_box(v_y_5045_);
v___x_5049_ = lean_obj_tag_nat(v___x_5048_);
lean_dec(v___x_5048_);
v___x_5050_ = lean_nat_dec_eq(v___x_5047_, v___x_5049_);
return v___x_5050_;
}
}
LEAN_EXPORT void l_Lean_Parser_instBEqLeadingIdentBehavior_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_5044_ = stack[0].m_num;
uint8_t v_y_5045_ = stack[1].m_num;
uint8_t v_res_5051_;
v_res_5051_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_5044_, v_y_5045_);
stack->m_num = v_res_5051_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_5052_, lean_object* v_y_5053_){
_start:
{
uint8_t v_x_24__boxed_5054_; uint8_t v_y_25__boxed_5055_; uint8_t v_res_5056_; lean_object* v_r_5057_; 
v_x_24__boxed_5054_ = lean_unbox(v_x_5052_);
v_y_25__boxed_5055_ = lean_unbox(v_y_5053_);
v_res_5056_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_24__boxed_5054_, v_y_25__boxed_5055_);
v_r_5057_ = lean_box(v_res_5056_);
return v_r_5057_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = lean_unsigned_to_nat(2u);
v___x_5070_ = lean_nat_to_int(v___x_5069_);
return v___x_5070_;
}
}
lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_5071_, lean_object* v_prec_5072_){
_start:
{
lean_object* v___y_5074_; lean_object* v___y_5081_; lean_object* v___y_5088_; 
switch(v_x_5071_)
{
case 0:
{
lean_object* v___x_5094_; uint8_t v___x_5095_; 
v___x_5094_ = lean_unsigned_to_nat(1024u);
v___x_5095_ = lean_nat_dec_le(v___x_5094_, v_prec_5072_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; 
v___x_5096_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_5074_ = v___x_5096_;
goto v___jp_5073_;
}
else
{
lean_object* v___x_5097_; 
v___x_5097_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_5074_ = v___x_5097_;
goto v___jp_5073_;
}
}
case 1:
{
lean_object* v___x_5098_; uint8_t v___x_5099_; 
v___x_5098_ = lean_unsigned_to_nat(1024u);
v___x_5099_ = lean_nat_dec_le(v___x_5098_, v_prec_5072_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; 
v___x_5100_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_5081_ = v___x_5100_;
goto v___jp_5080_;
}
else
{
lean_object* v___x_5101_; 
v___x_5101_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_5081_ = v___x_5101_;
goto v___jp_5080_;
}
}
default: 
{
lean_object* v___x_5102_; uint8_t v___x_5103_; 
v___x_5102_ = lean_unsigned_to_nat(1024u);
v___x_5103_ = lean_nat_dec_le(v___x_5102_, v_prec_5072_);
if (v___x_5103_ == 0)
{
lean_object* v___x_5104_; 
v___x_5104_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_5088_ = v___x_5104_;
goto v___jp_5087_;
}
else
{
lean_object* v___x_5105_; 
v___x_5105_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_5088_ = v___x_5105_;
goto v___jp_5087_;
}
}
}
v___jp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; uint8_t v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5075_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_5074_);
v___x_5076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___y_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = 0;
v___x_5078_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5078_, 0, v___x_5076_);
lean_ctor_set_uint8(v___x_5078_, sizeof(void*)*1, v___x_5077_);
v___x_5079_ = l_Repr_addAppParen(v___x_5078_, v_prec_5072_);
return v___x_5079_;
}
v___jp_5080_:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; uint8_t v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5082_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_5081_);
v___x_5083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5083_, 0, v___y_5081_);
lean_ctor_set(v___x_5083_, 1, v___x_5082_);
v___x_5084_ = 0;
v___x_5085_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5085_, 0, v___x_5083_);
lean_ctor_set_uint8(v___x_5085_, sizeof(void*)*1, v___x_5084_);
v___x_5086_ = l_Repr_addAppParen(v___x_5085_, v_prec_5072_);
return v___x_5086_;
}
v___jp_5087_:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; uint8_t v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5089_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_5088_);
v___x_5090_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5090_, 0, v___y_5088_);
lean_ctor_set(v___x_5090_, 1, v___x_5089_);
v___x_5091_ = 0;
v___x_5092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5092_, 0, v___x_5090_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1, v___x_5091_);
v___x_5093_ = l_Repr_addAppParen(v___x_5092_, v_prec_5072_);
return v___x_5093_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_instReprLeadingIdentBehavior_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_5071_ = stack[0].m_num;
lean_object* v_prec_5072_ = stack[1].m_obj;
lean_object* v_res_5106_;
v_res_5106_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_5071_, v_prec_5072_);
stack->m_obj
 = v_res_5106_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_5107_, lean_object* v_prec_5108_){
_start:
{
uint8_t v_x_169__boxed_5109_; lean_object* v_res_5110_; 
v_x_169__boxed_5109_ = lean_unbox(v_x_5107_);
v_res_5110_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_169__boxed_5109_, v_prec_5108_);
lean_dec(v_prec_5108_);
return v_res_5110_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_5113_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_5114_; lean_object* v___x_5115_; 
v___x_5114_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5115_, 0, v___x_5114_);
return v___x_5115_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5116_ = 0;
v___x_5117_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_5118_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_5119_ = lean_box(0);
v___x_5120_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5120_, 0, v___x_5119_);
lean_ctor_set(v___x_5120_, 1, v___x_5118_);
lean_ctor_set(v___x_5120_, 2, v___x_5117_);
lean_ctor_set_uint8(v___x_5120_, sizeof(void*)*3, v___x_5116_);
return v___x_5120_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_5121_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_5122_; 
v___x_5122_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_5122_;
}
}
lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_5123_, lean_object* v_c_5124_, lean_object* v_s_5125_, uint8_t v_behavior_5126_){
_start:
{
lean_object* v___x_5127_; lean_object* v_fst_5128_; lean_object* v_snd_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5171_; 
v___x_5127_ = l_Lean_Parser_peekToken(v_c_5124_, v_s_5125_);
v_fst_5128_ = lean_ctor_get(v___x_5127_, 0);
v_snd_5129_ = lean_ctor_get(v___x_5127_, 1);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5131_ = v___x_5127_;
v_isShared_5132_ = v_isSharedCheck_5171_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_snd_5129_);
lean_inc(v_fst_5128_);
lean_dec(v___x_5127_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5171_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v_n_5134_; 
if (lean_obj_tag(v_snd_5129_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
lean_del_object(v___x_5131_);
lean_dec(v_fst_5128_);
v_a_5146_ = lean_ctor_get(v_snd_5129_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v_snd_5129_, 1);
v___x_5147_ = lean_box(0);
v___x_5148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5148_, 0, v_a_5146_);
lean_ctor_set(v___x_5148_, 1, v___x_5147_);
return v___x_5148_;
}
else
{
lean_object* v_a_5149_; 
v_a_5149_ = lean_ctor_get(v_snd_5129_, 0);
lean_inc(v_a_5149_);
lean_dec_ref_known(v_snd_5129_, 1);
switch(lean_obj_tag(v_a_5149_))
{
case 2:
{
lean_object* v_val_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v_val_5150_ = lean_ctor_get(v_a_5149_, 1);
lean_inc_ref(v_val_5150_);
lean_dec_ref_known(v_a_5149_, 2);
v___x_5151_ = lean_box(0);
v___x_5152_ = l_Lean_Name_str___override(v___x_5151_, v_val_5150_);
v_n_5134_ = v___x_5152_;
goto v___jp_5133_;
}
case 3:
{
switch(v_behavior_5126_)
{
case 0:
{
lean_dec_ref_known(v_a_5149_, 4);
goto v___jp_5144_;
}
case 1:
{
lean_object* v_val_5153_; lean_object* v___x_5154_; 
v_val_5153_ = lean_ctor_get(v_a_5149_, 2);
lean_inc(v_val_5153_);
lean_dec_ref_known(v_a_5149_, 4);
v___x_5154_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5123_, v_val_5153_);
lean_dec(v_val_5153_);
if (lean_obj_tag(v___x_5154_) == 0)
{
goto v___jp_5144_;
}
else
{
lean_object* v_val_5155_; lean_object* v___x_5156_; 
lean_del_object(v___x_5131_);
v_val_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_val_5155_);
lean_dec_ref_known(v___x_5154_, 1);
v___x_5156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5156_, 0, v_fst_5128_);
lean_ctor_set(v___x_5156_, 1, v_val_5155_);
return v___x_5156_;
}
}
default: 
{
lean_object* v_val_5157_; lean_object* v___x_5158_; 
v_val_5157_ = lean_ctor_get(v_a_5149_, 2);
lean_inc(v_val_5157_);
lean_dec_ref_known(v_a_5149_, 4);
v___x_5158_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5123_, v_val_5157_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_dec(v_val_5157_);
goto v___jp_5144_;
}
else
{
lean_object* v_val_5159_; lean_object* v___x_5160_; uint8_t v___x_5161_; 
lean_del_object(v___x_5131_);
v_val_5159_ = lean_ctor_get(v___x_5158_, 0);
lean_inc(v_val_5159_);
lean_dec_ref_known(v___x_5158_, 1);
v___x_5160_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_5161_ = lean_name_eq(v_val_5157_, v___x_5160_);
lean_dec(v_val_5157_);
if (v___x_5161_ == 0)
{
lean_object* v___x_5162_; 
v___x_5162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5123_, v___x_5160_);
if (lean_obj_tag(v___x_5162_) == 1)
{
lean_object* v_val_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v_val_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_val_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v___x_5164_ = l_List_appendTR___redArg(v_val_5159_, v_val_5163_);
v___x_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5165_, 0, v_fst_5128_);
lean_ctor_set(v___x_5165_, 1, v___x_5164_);
return v___x_5165_;
}
else
{
lean_object* v___x_5166_; 
lean_dec(v___x_5162_);
v___x_5166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5166_, 0, v_fst_5128_);
lean_ctor_set(v___x_5166_, 1, v_val_5159_);
return v___x_5166_;
}
}
else
{
lean_object* v___x_5167_; 
v___x_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5167_, 0, v_fst_5128_);
lean_ctor_set(v___x_5167_, 1, v_val_5159_);
return v___x_5167_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_5168_; 
v_kind_5168_ = lean_ctor_get(v_a_5149_, 1);
lean_inc(v_kind_5168_);
lean_dec_ref_known(v_a_5149_, 3);
v_n_5134_ = v_kind_5168_;
goto v___jp_5133_;
}
default: 
{
lean_object* v___x_5169_; lean_object* v___x_5170_; 
lean_dec(v_a_5149_);
lean_del_object(v___x_5131_);
v___x_5169_ = lean_box(0);
v___x_5170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5170_, 0, v_fst_5128_);
lean_ctor_set(v___x_5170_, 1, v___x_5169_);
return v___x_5170_;
}
}
}
v___jp_5133_:
{
lean_object* v___x_5135_; 
v___x_5135_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5123_, v_n_5134_);
lean_dec(v_n_5134_);
if (lean_obj_tag(v___x_5135_) == 1)
{
lean_object* v_val_5136_; lean_object* v___x_5138_; 
v_val_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_val_5136_);
lean_dec_ref_known(v___x_5135_, 1);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 1, v_val_5136_);
v___x_5138_ = v___x_5131_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_fst_5128_);
lean_ctor_set(v_reuseFailAlloc_5139_, 1, v_val_5136_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
else
{
lean_object* v___x_5140_; lean_object* v___x_5142_; 
lean_dec(v___x_5135_);
v___x_5140_ = lean_box(0);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 1, v___x_5140_);
v___x_5142_ = v___x_5131_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_fst_5128_);
lean_ctor_set(v_reuseFailAlloc_5143_, 1, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
v___jp_5144_:
{
lean_object* v___x_5145_; 
v___x_5145_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_5134_ = v___x_5145_;
goto v___jp_5133_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_indexed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_5123_ = stack[0].m_obj;
lean_object* v_c_5124_ = stack[1].m_obj;
lean_object* v_s_5125_ = stack[2].m_obj;
uint8_t v_behavior_5126_ = stack[3].m_num;
lean_object* v_res_5172_;
v_res_5172_ = l_Lean_Parser_indexed___redArg(v_map_5123_, v_c_5124_, v_s_5125_, v_behavior_5126_);
stack->m_obj
 = v_res_5172_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_5173_, lean_object* v_c_5174_, lean_object* v_s_5175_, lean_object* v_behavior_5176_){
_start:
{
uint8_t v_behavior_boxed_5177_; lean_object* v_res_5178_; 
v_behavior_boxed_5177_ = lean_unbox(v_behavior_5176_);
v_res_5178_ = l_Lean_Parser_indexed___redArg(v_map_5173_, v_c_5174_, v_s_5175_, v_behavior_boxed_5177_);
lean_dec(v_map_5173_);
return v_res_5178_;
}
}
lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_5179_, lean_object* v_map_5180_, lean_object* v_c_5181_, lean_object* v_s_5182_, uint8_t v_behavior_5183_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_Lean_Parser_indexed___redArg(v_map_5180_, v_c_5181_, v_s_5182_, v_behavior_5183_);
return v___x_5184_;
}
}
LEAN_EXPORT void l_Lean_Parser_indexed_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_5180_ = stack[1].m_obj;
lean_object* v_c_5181_ = stack[2].m_obj;
lean_object* v_s_5182_ = stack[3].m_obj;
uint8_t v_behavior_5183_ = stack[4].m_num;
lean_object* v_res_5185_;
v_res_5185_ = l_Lean_Parser_indexed(lean_box(0), v_map_5180_, v_c_5181_, v_s_5182_, v_behavior_5183_);
stack->m_obj
 = v_res_5185_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_5186_, lean_object* v_map_5187_, lean_object* v_c_5188_, lean_object* v_s_5189_, lean_object* v_behavior_5190_){
_start:
{
uint8_t v_behavior_boxed_5191_; lean_object* v_res_5192_; 
v_behavior_boxed_5191_ = lean_unbox(v_behavior_5190_);
v_res_5192_ = l_Lean_Parser_indexed(v_00_u03b1_5186_, v_map_5187_, v_c_5188_, v_s_5189_, v_behavior_boxed_5191_);
lean_dec(v_map_5187_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_){
_start:
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Lean_Parser_whitespace(v___y_5194_, v___y_5195_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_5197_, v___y_5198_, v___y_5199_);
lean_dec(v_x_5197_);
return v_res_5200_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___f_5203_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_5204_ = lean_st_mk_ref(v___f_5203_);
v___x_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5204_);
return v___x_5205_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5206_;
v_res_5206_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5206_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_5208_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_5209_){
_start:
{
lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5211_ = lean_st_ref_get(v___x_5209_);
v___x_5212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5211_);
return v___x_5212_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5209_ = stack[0].m_obj;
lean_object* v_res_5213_;
v_res_5213_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_5209_);
stack->m_obj
 = v_res_5213_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_5214_);
lean_dec(v___x_5214_);
return v_res_5216_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5217_; lean_object* v___f_5218_; 
v___x_5217_ = l_Lean_Parser_categoryParserFnRef;
v___f_5218_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5218_, 0, v___x_5217_);
return v___f_5218_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; uint8_t v___x_5229_; lean_object* v___x_5230_; 
v___f_5225_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_5226_ = lean_box(0);
v___x_5227_ = lean_box(2);
v___x_5228_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_));
v___x_5229_ = 0;
v___x_5230_ = l_Lean_registerEnvExtension___redArg(v___f_5225_, v___x_5226_, v___x_5227_, v___x_5228_, v___x_5229_, v___x_5229_);
return v___x_5230_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5231_;
v_res_5231_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5231_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_5235_, v___y_5236_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_5238_, v___y_5239_, v___y_5240_);
lean_dec_ref(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v_a_5238_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_5245_, lean_object* v_ctx_5246_, lean_object* v_s_5247_){
_start:
{
lean_object* v_toParserModuleContext_5248_; lean_object* v_env_5249_; lean_object* v___x_5250_; lean_object* v_asyncMode_5251_; lean_object* v___f_5252_; lean_object* v___x_5253_; uint8_t v___x_5254_; lean_object* v___x_21__overap_5255_; lean_object* v___x_5256_; 
v_toParserModuleContext_5248_ = lean_ctor_get(v_ctx_5246_, 1);
v_env_5249_ = lean_ctor_get(v_toParserModuleContext_5248_, 0);
v___x_5250_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_5251_ = lean_ctor_get(v___x_5250_, 2);
v___f_5252_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_5253_ = lean_box(0);
v___x_5254_ = 0;
lean_inc_ref(v_env_5249_);
v___x_21__overap_5255_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_5252_, v___x_5250_, v_env_5249_, v_asyncMode_5251_, v___x_5253_, v___x_5254_);
v___x_5256_ = lean_apply_3(v___x_21__overap_5255_, v_catName_5245_, v_ctx_5246_, v_s_5247_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_5257_, lean_object* v_x_5258_){
_start:
{
lean_object* v_quotDepth_5259_; uint8_t v_suppressInsideQuot_5260_; lean_object* v_savedPos_x3f_5261_; lean_object* v_forbiddenTks_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
v_quotDepth_5259_ = lean_ctor_get(v_x_5258_, 1);
v_suppressInsideQuot_5260_ = lean_ctor_get_uint8(v_x_5258_, sizeof(void*)*4);
v_savedPos_x3f_5261_ = lean_ctor_get(v_x_5258_, 2);
v_forbiddenTks_5262_ = lean_ctor_get(v_x_5258_, 3);
v_isSharedCheck_5269_ = !lean_is_exclusive(v_x_5258_);
if (v_isSharedCheck_5269_ == 0)
{
lean_object* v_unused_5270_; 
v_unused_5270_ = lean_ctor_get(v_x_5258_, 0);
lean_dec(v_unused_5270_);
v___x_5264_ = v_x_5258_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_forbiddenTks_5262_);
lean_inc(v_savedPos_x3f_5261_);
lean_inc(v_quotDepth_5259_);
lean_dec(v_x_5258_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 0, v_prec_5257_);
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_prec_5257_);
lean_ctor_set(v_reuseFailAlloc_5268_, 1, v_quotDepth_5259_);
lean_ctor_set(v_reuseFailAlloc_5268_, 2, v_savedPos_x3f_5261_);
lean_ctor_set(v_reuseFailAlloc_5268_, 3, v_forbiddenTks_5262_);
lean_ctor_set_uint8(v_reuseFailAlloc_5268_, sizeof(void*)*4, v_suppressInsideQuot_5260_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_5271_, lean_object* v_prec_5272_){
_start:
{
lean_object* v___f_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___f_5273_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_5273_, 0, v_prec_5272_);
v___x_5274_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_5271_);
v___x_5275_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_5275_, 0, v_catName_5271_);
v___x_5276_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_5276_, 0, v_catName_5271_);
lean_closure_set(v___x_5276_, 1, v___x_5275_);
v___x_5277_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5277_, 0, v___f_5273_);
lean_closure_set(v___x_5277_, 1, v___x_5276_);
v___x_5278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5274_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5282_){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5283_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5284_ = l_Lean_Parser_categoryParser(v___x_5283_, v_prec_5282_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5286_, lean_object* v_s_5287_){
_start:
{
lean_object* v_stxStack_5288_; lean_object* v_pos_5289_; lean_object* v_prev_5290_; uint8_t v___x_5291_; 
v_stxStack_5288_ = lean_ctor_get(v_s_5287_, 0);
v_pos_5289_ = lean_ctor_get(v_s_5287_, 2);
v_prev_5290_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5288_);
v___x_5291_ = l_Lean_Parser_checkTailNoWs(v_prev_5290_);
lean_dec(v_prev_5290_);
if (v___x_5291_ == 0)
{
return v_s_5287_;
}
else
{
lean_object* v_toInputContext_5292_; uint8_t v___x_5293_; 
v_toInputContext_5292_ = lean_ctor_get(v_c_5286_, 0);
v___x_5293_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5292_, v_pos_5289_);
if (v___x_5293_ == 0)
{
lean_object* v_inputString_5294_; uint32_t v_curr_5295_; uint32_t v___x_5296_; uint8_t v___x_5297_; 
v_inputString_5294_ = lean_ctor_get(v_toInputContext_5292_, 0);
v_curr_5295_ = lean_string_utf8_get_fast(v_inputString_5294_, v_pos_5289_);
v___x_5296_ = 58;
v___x_5297_ = lean_uint32_dec_eq(v_curr_5295_, v___x_5296_);
if (v___x_5297_ == 0)
{
return v_s_5287_;
}
else
{
lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5298_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5299_ = lean_box(0);
v___x_5300_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5287_, v___x_5298_, v___x_5299_, v___x_5297_);
return v___x_5300_;
}
}
else
{
return v_s_5287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5301_, lean_object* v_s_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5301_, v_s_5302_);
lean_dec_ref(v_c_5301_);
return v_res_5303_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5317_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5318_ = l_Lean_addBuiltinDocString(v___x_5316_, v___x_5317_);
return v___x_5318_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5319_;
v_res_5319_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
stack->m_obj
 = v_res_5319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5322_, lean_object* v_p_5323_, lean_object* v_c_5324_, lean_object* v_s_5325_){
_start:
{
lean_object* v___x_5326_; lean_object* v_errorMsg_5327_; 
v___x_5326_ = lean_apply_2(v_p_5323_, v_c_5324_, v_s_5325_);
v_errorMsg_5327_ = lean_ctor_get(v___x_5326_, 4);
lean_inc(v_errorMsg_5327_);
if (lean_obj_tag(v_errorMsg_5327_) == 1)
{
lean_object* v_val_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5358_; 
v_val_5328_ = lean_ctor_get(v_errorMsg_5327_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v_errorMsg_5327_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5330_ = v_errorMsg_5327_;
v_isShared_5331_ = v_isSharedCheck_5358_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_val_5328_);
lean_dec(v_errorMsg_5327_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5358_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v_stxStack_5332_; lean_object* v_lhsPrec_5333_; lean_object* v_pos_5334_; lean_object* v_cache_5335_; lean_object* v_recoveredErrors_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5356_; 
v_stxStack_5332_ = lean_ctor_get(v___x_5326_, 0);
v_lhsPrec_5333_ = lean_ctor_get(v___x_5326_, 1);
v_pos_5334_ = lean_ctor_get(v___x_5326_, 2);
v_cache_5335_ = lean_ctor_get(v___x_5326_, 3);
v_recoveredErrors_5336_ = lean_ctor_get(v___x_5326_, 5);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; 
v_unused_5357_ = lean_ctor_get(v___x_5326_, 4);
lean_dec(v_unused_5357_);
v___x_5338_ = v___x_5326_;
v_isShared_5339_ = v_isSharedCheck_5356_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_recoveredErrors_5336_);
lean_inc(v_cache_5335_);
lean_inc(v_pos_5334_);
lean_inc(v_lhsPrec_5333_);
lean_inc(v_stxStack_5332_);
lean_dec(v___x_5326_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5356_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v_unexpectedTk_5340_; lean_object* v_unexpected_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5354_; 
v_unexpectedTk_5340_ = lean_ctor_get(v_val_5328_, 0);
v_unexpected_5341_ = lean_ctor_get(v_val_5328_, 1);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_val_5328_);
if (v_isSharedCheck_5354_ == 0)
{
lean_object* v_unused_5355_; 
v_unused_5355_ = lean_ctor_get(v_val_5328_, 2);
lean_dec(v_unused_5355_);
v___x_5343_ = v_val_5328_;
v_isShared_5344_ = v_isSharedCheck_5354_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_unexpected_5341_);
lean_inc(v_unexpectedTk_5340_);
lean_dec(v_val_5328_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5354_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5346_; 
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 2, v_expected_5322_);
v___x_5346_ = v___x_5343_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_unexpectedTk_5340_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v_unexpected_5341_);
lean_ctor_set(v_reuseFailAlloc_5353_, 2, v_expected_5322_);
v___x_5346_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5348_; 
if (v_isShared_5331_ == 0)
{
lean_ctor_set(v___x_5330_, 0, v___x_5346_);
v___x_5348_ = v___x_5330_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5350_; 
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 4, v___x_5348_);
v___x_5350_ = v___x_5338_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_stxStack_5332_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v_lhsPrec_5333_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v_pos_5334_);
lean_ctor_set(v_reuseFailAlloc_5351_, 3, v_cache_5335_);
lean_ctor_set(v_reuseFailAlloc_5351_, 4, v___x_5348_);
lean_ctor_set(v_reuseFailAlloc_5351_, 5, v_recoveredErrors_5336_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5327_);
lean_dec(v_expected_5322_);
return v___x_5326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5359_, lean_object* v_p_5360_){
_start:
{
lean_object* v_info_5361_; lean_object* v_fn_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5370_; 
v_info_5361_ = lean_ctor_get(v_p_5360_, 0);
v_fn_5362_ = lean_ctor_get(v_p_5360_, 1);
v_isSharedCheck_5370_ = !lean_is_exclusive(v_p_5360_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5364_ = v_p_5360_;
v_isShared_5365_ = v_isSharedCheck_5370_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_fn_5362_);
lean_inc(v_info_5361_);
lean_dec(v_p_5360_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5370_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5366_; lean_object* v___x_5368_; 
v___x_5366_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5366_, 0, v_expected_5359_);
lean_closure_set(v___x_5366_, 1, v_fn_5362_);
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 1, v___x_5366_);
v___x_5368_ = v___x_5364_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_info_5361_);
lean_ctor_set(v_reuseFailAlloc_5369_, 1, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5371_, lean_object* v_s_5372_){
_start:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; 
v___x_5373_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_5374_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5372_, v___x_5373_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5375_, lean_object* v_s_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_Parser_pushNone___lam__0(v_x_5375_, v_s_5376_);
lean_dec_ref(v_x_5375_);
return v_res_5377_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5387_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5388_ = l_Lean_Parser_symbolNoAntiquot(v___x_5387_);
return v___x_5388_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = lean_unsigned_to_nat(0u);
v___x_5390_ = l_Lean_Parser_termParser(v___x_5389_);
return v___x_5390_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5392_ = l_Lean_Parser_decQuotDepth(v___x_5391_);
return v___x_5392_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5393_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5394_ = l_Lean_Parser_symbolNoAntiquot(v___x_5393_);
return v___x_5394_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5396_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5397_ = l_Lean_Parser_andthen(v___x_5396_, v___x_5395_);
return v___x_5397_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5398_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5399_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5400_ = l_Lean_Parser_andthen(v___x_5399_, v___x_5398_);
return v___x_5400_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5401_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5402_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5403_ = l_Lean_Parser_node(v___x_5402_, v___x_5401_);
return v___x_5403_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5404_; 
v___x_5404_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5404_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5406_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5407_ = l_Lean_Parser_symbolNoAntiquot(v___x_5406_);
return v___x_5407_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5408_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5409_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5410_ = l_Lean_Parser_orelse(v___x_5409_, v___x_5408_);
return v___x_5410_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5411_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5412_ = l_Lean_Parser_identNoAntiquot;
v___x_5413_ = l_Lean_Parser_orelse(v___x_5412_, v___x_5411_);
return v___x_5413_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5414_; 
v___x_5414_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5414_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5417_ = l_Lean_Parser_checkNoWsBefore(v___x_5416_);
return v___x_5417_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5419_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5420_ = l_Lean_Parser_symbolNoAntiquot(v___x_5419_);
return v___x_5420_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; 
v___x_5422_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5423_ = l_Lean_Parser_symbolNoAntiquot(v___x_5422_);
return v___x_5423_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5424_ = l_Lean_Parser_antiquotExpr;
v___x_5425_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5426_ = l_Lean_Parser_andthen(v___x_5425_, v___x_5424_);
return v___x_5426_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5427_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5428_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5429_ = l_Lean_Parser_andthen(v___x_5428_, v___x_5427_);
return v___x_5429_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5430_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5431_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5432_ = l_Lean_Parser_andthen(v___x_5431_, v___x_5430_);
return v___x_5432_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5433_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5434_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5435_ = l_Lean_Parser_andthen(v___x_5434_, v___x_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5439_, lean_object* v_s_5440_){
_start:
{
lean_object* v_pos_5441_; lean_object* v_errorMsg_5442_; lean_object* v___x_5443_; uint8_t v___x_5444_; 
v_pos_5441_ = lean_ctor_get(v_s_5440_, 2);
v_errorMsg_5442_ = lean_ctor_get(v_s_5440_, 4);
v___x_5443_ = lean_box(0);
v___x_5444_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5442_, v___x_5443_);
if (v___x_5444_ == 0)
{
lean_dec_ref(v_c_5439_);
return v_s_5440_;
}
else
{
lean_object* v___x_5445_; lean_object* v_fn_5446_; lean_object* v_iniSz_5447_; lean_object* v_s_5448_; lean_object* v_errorMsg_5449_; uint8_t v___x_5450_; 
lean_inc(v_pos_5441_);
v___x_5445_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5446_ = lean_ctor_get(v___x_5445_, 1);
v_iniSz_5447_ = l_Lean_Parser_ParserState_stackSize(v_s_5440_);
lean_inc_ref(v_fn_5446_);
v_s_5448_ = lean_apply_2(v_fn_5446_, v_c_5439_, v_s_5440_);
v_errorMsg_5449_ = lean_ctor_get(v_s_5448_, 4);
lean_inc(v_errorMsg_5449_);
v___x_5450_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5449_, v___x_5443_);
lean_dec(v_errorMsg_5449_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; 
v___x_5451_ = l_Lean_Parser_ParserState_restore(v_s_5448_, v_iniSz_5447_, v_pos_5441_);
lean_dec(v_iniSz_5447_);
return v___x_5451_;
}
else
{
lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
lean_dec(v_pos_5441_);
v___x_5452_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5453_ = lean_unsigned_to_nat(1u);
v___x_5454_ = lean_nat_sub(v_iniSz_5447_, v___x_5453_);
lean_dec(v_iniSz_5447_);
v___x_5455_ = l_Lean_Parser_ParserState_mkNode(v_s_5448_, v___x_5452_, v___x_5454_);
lean_dec(v___x_5454_);
return v___x_5455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v_toInputContext_5459_; lean_object* v_s_5460_; lean_object* v_pos_5461_; lean_object* v_inputString_5462_; uint32_t v___x_5463_; uint32_t v___x_5464_; uint8_t v___x_5465_; 
v_toInputContext_5459_ = lean_ctor_get(v___y_5457_, 0);
lean_inc_ref(v___y_5457_);
v_s_5460_ = lean_apply_2(v_fn_5456_, v___y_5457_, v___y_5458_);
v_pos_5461_ = lean_ctor_get(v_s_5460_, 2);
lean_inc(v_pos_5461_);
v_inputString_5462_ = lean_ctor_get(v_toInputContext_5459_, 0);
v___x_5463_ = lean_string_utf8_get(v_inputString_5462_, v_pos_5461_);
lean_dec(v_pos_5461_);
v___x_5464_ = 37;
v___x_5465_ = lean_uint32_dec_eq(v___x_5463_, v___x_5464_);
if (v___x_5465_ == 0)
{
lean_dec_ref(v___y_5457_);
return v_s_5460_;
}
else
{
lean_object* v___x_5466_; 
v___x_5466_ = l_Lean_Parser_tokenAntiquotFn(v___y_5457_, v_s_5460_);
return v___x_5466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5467_){
_start:
{
lean_object* v_info_5468_; lean_object* v_fn_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5477_; 
v_info_5468_ = lean_ctor_get(v_p_5467_, 0);
v_fn_5469_ = lean_ctor_get(v_p_5467_, 1);
v_isSharedCheck_5477_ = !lean_is_exclusive(v_p_5467_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5471_ = v_p_5467_;
v_isShared_5472_ = v_isSharedCheck_5477_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_fn_5469_);
lean_inc(v_info_5468_);
lean_dec(v_p_5467_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5477_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___f_5473_; lean_object* v___x_5475_; 
v___f_5473_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5473_, 0, v_fn_5469_);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 1, v___f_5473_);
v___x_5475_ = v___x_5471_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_info_5468_);
lean_ctor_set(v_reuseFailAlloc_5476_, 1, v___f_5473_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5478_){
_start:
{
lean_object* v___x_5479_; lean_object* v___x_5480_; 
v___x_5479_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5478_);
v___x_5480_ = l_Lean_Parser_tokenWithAntiquot(v___x_5479_);
return v___x_5480_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5483_, uint8_t v_includeIdent_5484_){
_start:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5485_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5483_, v_includeIdent_5484_);
v___x_5486_ = l_Lean_Parser_tokenWithAntiquot(v___x_5485_);
return v___x_5486_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_5483_ = stack[0].m_obj;
uint8_t v_includeIdent_5484_ = stack[1].m_num;
lean_object* v_res_5487_;
v_res_5487_ = l_Lean_Parser_nonReservedSymbol(v_sym_5483_, v_includeIdent_5484_);
stack->m_obj
 = v_res_5487_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5488_, lean_object* v_includeIdent_5489_){
_start:
{
uint8_t v_includeIdent_boxed_5490_; lean_object* v_res_5491_; 
v_includeIdent_boxed_5490_ = lean_unbox(v_includeIdent_5489_);
v_res_5491_ = l_Lean_Parser_nonReservedSymbol(v_sym_5488_, v_includeIdent_boxed_5490_);
return v_res_5491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5492_, lean_object* v_asciiSym_5493_){
_start:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5492_, v_asciiSym_5493_);
v___x_5495_ = l_Lean_Parser_tokenWithAntiquot(v___x_5494_);
return v___x_5495_;
}
}
lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5496_, lean_object* v_asciiSym_5497_, uint8_t v_preserveForPP_5498_){
_start:
{
lean_object* v___x_5499_; 
v___x_5499_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5496_, v_asciiSym_5497_);
return v___x_5499_;
}
}
LEAN_EXPORT void l_Lean_Parser_unicodeSymbol_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_5496_ = stack[0].m_obj;
lean_object* v_asciiSym_5497_ = stack[1].m_obj;
uint8_t v_preserveForPP_5498_ = stack[2].m_num;
lean_object* v_res_5500_;
v_res_5500_ = l_Lean_Parser_unicodeSymbol(v_sym_5496_, v_asciiSym_5497_, v_preserveForPP_5498_);
stack->m_obj
 = v_res_5500_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5501_, lean_object* v_asciiSym_5502_, lean_object* v_preserveForPP_5503_){
_start:
{
uint8_t v_preserveForPP_boxed_5504_; lean_object* v_res_5505_; 
v_preserveForPP_boxed_5504_ = lean_unbox(v_preserveForPP_5503_);
v_res_5505_ = l_Lean_Parser_unicodeSymbol(v_sym_5501_, v_asciiSym_5502_, v_preserveForPP_boxed_5504_);
return v_res_5505_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___x_5506_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5507_ = l_Lean_Parser_symbol(v___x_5506_);
return v___x_5507_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v___x_5508_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5509_ = lean_box(0);
v___x_5510_ = l_Lean_Parser_setExpected(v___x_5509_, v___x_5508_);
return v___x_5510_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; 
v___x_5511_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5512_ = l_Lean_Parser_checkNoWsBefore(v___x_5511_);
return v___x_5512_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5513_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5514_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5515_ = l_Lean_Parser_andthen(v___x_5514_, v___x_5513_);
return v___x_5515_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5516_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5517_ = l_Lean_Parser_manyNoAntiquot(v___x_5516_);
return v___x_5517_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; 
v___x_5519_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5520_ = l_Lean_Parser_checkNoWsBefore(v___x_5519_);
return v___x_5520_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5529_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5530_ = l_Lean_Parser_symbol(v___x_5529_);
return v___x_5530_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5531_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5532_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5533_ = l_Lean_Parser_andthen(v___x_5532_, v___x_5531_);
return v___x_5533_;
}
}
lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5537_, lean_object* v_kind_5538_, uint8_t v_anonymous_5539_, uint8_t v_isPseudoKind_5540_){
_start:
{
lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5556_; 
if (v_isPseudoKind_5540_ == 0)
{
lean_object* v___x_5574_; 
v___x_5574_ = lean_box(0);
v___y_5556_ = v___x_5574_;
goto v___jp_5555_;
}
else
{
lean_object* v___x_5575_; 
v___x_5575_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5556_ = v___x_5575_;
goto v___jp_5555_;
}
v___jp_5541_:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5544_ = l_Lean_Parser_maxPrec;
v___x_5545_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5546_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5547_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5548_ = l_Lean_Parser_antiquotExpr;
v___x_5549_ = l_Lean_Parser_andthen(v___x_5548_, v___y_5543_);
v___x_5550_ = l_Lean_Parser_andthen(v___x_5547_, v___x_5549_);
v___x_5551_ = l_Lean_Parser_andthen(v___x_5546_, v___x_5550_);
v___x_5552_ = l_Lean_Parser_andthen(v___x_5545_, v___x_5551_);
v___x_5553_ = l_Lean_Parser_atomic(v___x_5552_);
v___x_5554_ = l_Lean_Parser_leadingNode(v___y_5542_, v___x_5544_, v___x_5553_);
return v___x_5554_;
}
v___jp_5555_:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v_kind_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; uint8_t v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v_nameP_5571_; 
lean_inc(v___y_5556_);
v___x_5557_ = l_Lean_Name_append(v_kind_5538_, v___y_5556_);
v___x_5558_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5559_ = l_Lean_Name_append(v___x_5557_, v___x_5558_);
v___x_5560_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5561_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5562_ = lean_string_append(v___x_5561_, v_name_5537_);
v___x_5563_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5564_ = lean_string_append(v___x_5562_, v___x_5563_);
v___x_5565_ = l_Lean_Parser_checkNoWsBefore(v___x_5564_);
v___x_5566_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5567_ = 0;
v___x_5568_ = l_Lean_Parser_nonReservedSymbol(v_name_5537_, v___x_5567_);
v___x_5569_ = l_Lean_Parser_andthen(v___x_5566_, v___x_5568_);
v___x_5570_ = l_Lean_Parser_andthen(v___x_5565_, v___x_5569_);
v_nameP_5571_ = l_Lean_Parser_node(v___x_5560_, v___x_5570_);
if (v_anonymous_5539_ == 0)
{
v___y_5542_ = v_kind_5559_;
v___y_5543_ = v_nameP_5571_;
goto v___jp_5541_;
}
else
{
lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5572_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5573_ = l_Lean_Parser_orelse(v_nameP_5571_, v___x_5572_);
v___y_5542_ = v_kind_5559_;
v___y_5543_ = v___x_5573_;
goto v___jp_5541_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_5537_ = stack[0].m_obj;
lean_object* v_kind_5538_ = stack[1].m_obj;
uint8_t v_anonymous_5539_ = stack[2].m_num;
uint8_t v_isPseudoKind_5540_ = stack[3].m_num;
lean_object* v_res_5576_;
v_res_5576_ = l_Lean_Parser_mkAntiquot(v_name_5537_, v_kind_5538_, v_anonymous_5539_, v_isPseudoKind_5540_);
stack->m_obj
 = v_res_5576_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5577_, lean_object* v_kind_5578_, lean_object* v_anonymous_5579_, lean_object* v_isPseudoKind_5580_){
_start:
{
uint8_t v_anonymous_boxed_5581_; uint8_t v_isPseudoKind_boxed_5582_; lean_object* v_res_5583_; 
v_anonymous_boxed_5581_ = lean_unbox(v_anonymous_5579_);
v_isPseudoKind_boxed_5582_ = lean_unbox(v_isPseudoKind_5580_);
v_res_5583_ = l_Lean_Parser_mkAntiquot(v_name_5577_, v_kind_5578_, v_anonymous_boxed_5581_, v_isPseudoKind_boxed_5582_);
return v_res_5583_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_5591_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5592_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5593_ = l_Lean_addBuiltinDocString(v___x_5591_, v___x_5592_);
return v___x_5593_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5594_;
v_res_5594_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
stack->m_obj
 = v_res_5594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5596_;
}
}
lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5597_, lean_object* v_p_5598_, uint8_t v_antiquotBehavior_5599_, lean_object* v_c_5600_, lean_object* v_s_5601_){
_start:
{
lean_object* v_toInputContext_5602_; lean_object* v_pos_5603_; lean_object* v_inputString_5604_; uint32_t v___x_5605_; uint32_t v___x_5606_; uint8_t v___x_5607_; 
v_toInputContext_5602_ = lean_ctor_get(v_c_5600_, 0);
v_pos_5603_ = lean_ctor_get(v_s_5601_, 2);
v_inputString_5604_ = lean_ctor_get(v_toInputContext_5602_, 0);
v___x_5605_ = lean_string_utf8_get(v_inputString_5604_, v_pos_5603_);
v___x_5606_ = 36;
v___x_5607_ = lean_uint32_dec_eq(v___x_5605_, v___x_5606_);
if (v___x_5607_ == 0)
{
lean_object* v___x_5608_; 
lean_dec_ref(v_antiquotP_5597_);
v___x_5608_ = lean_apply_2(v_p_5598_, v_c_5600_, v_s_5601_);
return v___x_5608_;
}
else
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5597_, v_p_5598_, v_antiquotBehavior_5599_, v_c_5600_, v_s_5601_);
return v___x_5609_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_withAntiquotFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_antiquotP_5597_ = stack[0].m_obj;
lean_object* v_p_5598_ = stack[1].m_obj;
uint8_t v_antiquotBehavior_5599_ = stack[2].m_num;
lean_object* v_c_5600_ = stack[3].m_obj;
lean_object* v_s_5601_ = stack[4].m_obj;
lean_object* v_res_5610_;
v_res_5610_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5597_, v_p_5598_, v_antiquotBehavior_5599_, v_c_5600_, v_s_5601_);
stack->m_obj
 = v_res_5610_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5611_, lean_object* v_p_5612_, lean_object* v_antiquotBehavior_5613_, lean_object* v_c_5614_, lean_object* v_s_5615_){
_start:
{
uint8_t v_antiquotBehavior_boxed_5616_; lean_object* v_res_5617_; 
v_antiquotBehavior_boxed_5616_ = lean_unbox(v_antiquotBehavior_5613_);
v_res_5617_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5611_, v_p_5612_, v_antiquotBehavior_boxed_5616_, v_c_5614_, v_s_5615_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5618_, lean_object* v_p_5619_){
_start:
{
lean_object* v_info_5620_; lean_object* v_fn_5621_; lean_object* v_info_5622_; lean_object* v_fn_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5634_; 
v_info_5620_ = lean_ctor_get(v_antiquotP_5618_, 0);
lean_inc_ref(v_info_5620_);
v_fn_5621_ = lean_ctor_get(v_antiquotP_5618_, 1);
lean_inc_ref(v_fn_5621_);
lean_dec_ref(v_antiquotP_5618_);
v_info_5622_ = lean_ctor_get(v_p_5619_, 0);
v_fn_5623_ = lean_ctor_get(v_p_5619_, 1);
v_isSharedCheck_5634_ = !lean_is_exclusive(v_p_5619_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5625_ = v_p_5619_;
v_isShared_5626_ = v_isSharedCheck_5634_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_fn_5623_);
lean_inc(v_info_5622_);
lean_dec(v_p_5619_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5634_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5627_; uint8_t v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5632_; 
v___x_5627_ = l_Lean_Parser_orelseInfo(v_info_5620_, v_info_5622_);
v___x_5628_ = 1;
v___x_5629_ = lean_box(v___x_5628_);
v___x_5630_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5630_, 0, v_fn_5621_);
lean_closure_set(v___x_5630_, 1, v_fn_5623_);
lean_closure_set(v___x_5630_, 2, v___x_5629_);
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5630_);
lean_ctor_set(v___x_5625_, 0, v___x_5627_);
v___x_5632_ = v___x_5625_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5627_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; 
v___x_5642_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5643_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5644_ = l_Lean_addBuiltinDocString(v___x_5642_, v___x_5643_);
return v___x_5644_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5645_;
v_res_5645_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
stack->m_obj
 = v_res_5645_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5646_){
_start:
{
lean_object* v_res_5647_; 
v_res_5647_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotAcceptLhs(lean_object* v_antiquotP_5648_, lean_object* v_p_5649_){
_start:
{
lean_object* v_info_5650_; lean_object* v_fn_5651_; lean_object* v_info_5652_; lean_object* v_fn_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5664_; 
v_info_5650_ = lean_ctor_get(v_antiquotP_5648_, 0);
lean_inc_ref(v_info_5650_);
v_fn_5651_ = lean_ctor_get(v_antiquotP_5648_, 1);
lean_inc_ref(v_fn_5651_);
lean_dec_ref(v_antiquotP_5648_);
v_info_5652_ = lean_ctor_get(v_p_5649_, 0);
v_fn_5653_ = lean_ctor_get(v_p_5649_, 1);
v_isSharedCheck_5664_ = !lean_is_exclusive(v_p_5649_);
if (v_isSharedCheck_5664_ == 0)
{
v___x_5655_ = v_p_5649_;
v_isShared_5656_ = v_isSharedCheck_5664_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_fn_5653_);
lean_inc(v_info_5652_);
lean_dec(v_p_5649_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5664_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5657_; uint8_t v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5662_; 
v___x_5657_ = l_Lean_Parser_orelseInfo(v_info_5650_, v_info_5652_);
v___x_5658_ = 0;
v___x_5659_ = lean_box(v___x_5658_);
v___x_5660_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5660_, 0, v_fn_5651_);
lean_closure_set(v___x_5660_, 1, v_fn_5653_);
lean_closure_set(v___x_5660_, 2, v___x_5659_);
if (v_isShared_5656_ == 0)
{
lean_ctor_set(v___x_5655_, 1, v___x_5660_);
lean_ctor_set(v___x_5655_, 0, v___x_5657_);
v___x_5662_ = v___x_5655_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v___x_5657_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v___x_5660_);
v___x_5662_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
return v___x_5662_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1(){
_start:
{
lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; 
v___x_5672_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1));
v___x_5673_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__2));
v___x_5674_ = l_Lean_addBuiltinDocString(v___x_5672_, v___x_5673_);
return v___x_5674_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5675_;
v_res_5675_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1();
stack->m_obj
 = v_res_5675_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___boxed(lean_object* v_a_5676_){
_start:
{
lean_object* v_res_5677_; 
v_res_5677_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1();
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5678_){
_start:
{
lean_object* v_fn_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5687_; 
v_fn_5679_ = lean_ctor_get(v_p_5678_, 1);
v_isSharedCheck_5687_ = !lean_is_exclusive(v_p_5678_);
if (v_isSharedCheck_5687_ == 0)
{
lean_object* v_unused_5688_; 
v_unused_5688_ = lean_ctor_get(v_p_5678_, 0);
lean_dec(v_unused_5688_);
v___x_5681_ = v_p_5678_;
v_isShared_5682_ = v_isSharedCheck_5687_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_fn_5679_);
lean_dec(v_p_5678_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5687_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v___x_5683_; lean_object* v___x_5685_; 
v___x_5683_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 0, v___x_5683_);
v___x_5685_ = v___x_5681_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5683_);
lean_ctor_set(v_reuseFailAlloc_5686_, 1, v_fn_5679_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5692_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5693_ = l_Lean_Parser_symbol(v___x_5692_);
return v___x_5693_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5694_; lean_object* v___x_5695_; 
v___x_5694_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5695_ = l_Lean_Parser_symbol(v___x_5694_);
return v___x_5695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5696_, lean_object* v_p_5697_, lean_object* v_suffix_5698_){
_start:
{
lean_object* v___x_5699_; lean_object* v_kind_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5699_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5700_ = l_Lean_Name_append(v_kind_5696_, v___x_5699_);
v___x_5701_ = l_Lean_Parser_maxPrec;
v___x_5702_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5703_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5704_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5705_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5706_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5707_ = l_Lean_Parser_node(v___x_5706_, v_p_5697_);
v___x_5708_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5709_ = l_Lean_Parser_andthen(v___x_5708_, v_suffix_5698_);
v___x_5710_ = l_Lean_Parser_andthen(v___x_5707_, v___x_5709_);
v___x_5711_ = l_Lean_Parser_andthen(v___x_5705_, v___x_5710_);
v___x_5712_ = l_Lean_Parser_andthen(v___x_5704_, v___x_5711_);
v___x_5713_ = l_Lean_Parser_andthen(v___x_5703_, v___x_5712_);
v___x_5714_ = l_Lean_Parser_andthen(v___x_5702_, v___x_5713_);
v___x_5715_ = l_Lean_Parser_atomic(v___x_5714_);
v___x_5716_ = l_Lean_Parser_leadingNode(v_kind_5700_, v___x_5701_, v___x_5715_);
return v___x_5716_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; 
v___x_5724_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5725_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5726_ = l_Lean_addBuiltinDocString(v___x_5724_, v___x_5725_);
return v___x_5726_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5727_;
v_res_5727_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
stack->m_obj
 = v_res_5727_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5728_){
_start:
{
lean_object* v_res_5729_; 
v_res_5729_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5733_, lean_object* v_suffix_5734_, lean_object* v_c_5735_, lean_object* v_s_5736_){
_start:
{
lean_object* v_pos_5737_; lean_object* v_iniSz_5738_; lean_object* v_s_5739_; lean_object* v_stxStack_5740_; lean_object* v_errorMsg_5741_; lean_object* v___x_5742_; uint8_t v___x_5743_; 
v_pos_5737_ = lean_ctor_get(v_s_5736_, 2);
lean_inc(v_pos_5737_);
v_iniSz_5738_ = l_Lean_Parser_ParserState_stackSize(v_s_5736_);
v_s_5739_ = lean_apply_2(v_suffix_5734_, v_c_5735_, v_s_5736_);
v_stxStack_5740_ = lean_ctor_get(v_s_5739_, 0);
lean_inc_ref(v_stxStack_5740_);
v_errorMsg_5741_ = lean_ctor_get(v_s_5739_, 4);
lean_inc(v_errorMsg_5741_);
v___x_5742_ = lean_box(0);
v___x_5743_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5741_, v___x_5742_);
lean_dec(v_errorMsg_5741_);
if (v___x_5743_ == 0)
{
lean_object* v___x_5744_; 
lean_dec_ref(v_stxStack_5740_);
lean_dec(v_kind_5733_);
v___x_5744_ = l_Lean_Parser_ParserState_restore(v_s_5739_, v_iniSz_5738_, v_pos_5737_);
lean_dec(v_iniSz_5738_);
return v___x_5744_;
}
else
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; 
lean_dec(v_iniSz_5738_);
lean_dec(v_pos_5737_);
v___x_5745_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5746_ = l_Lean_Name_append(v_kind_5733_, v___x_5745_);
v___x_5747_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5740_);
lean_dec_ref(v_stxStack_5740_);
v___x_5748_ = lean_unsigned_to_nat(2u);
v___x_5749_ = lean_nat_sub(v___x_5747_, v___x_5748_);
lean_dec(v___x_5747_);
v___x_5750_ = l_Lean_Parser_ParserState_mkNode(v_s_5739_, v___x_5746_, v___x_5749_);
lean_dec(v___x_5749_);
return v___x_5750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5751_, lean_object* v_kind_5752_, lean_object* v_fn_5753_, lean_object* v_c_5754_, lean_object* v_s_5755_){
_start:
{
lean_object* v_s_5756_; lean_object* v_stxStack_5757_; lean_object* v_errorMsg_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; 
lean_inc_ref(v_c_5754_);
v_s_5756_ = lean_apply_2(v_fn_5751_, v_c_5754_, v_s_5755_);
v_stxStack_5757_ = lean_ctor_get(v_s_5756_, 0);
lean_inc_ref(v_stxStack_5757_);
v_errorMsg_5758_ = lean_ctor_get(v_s_5756_, 4);
lean_inc(v_errorMsg_5758_);
v___x_5759_ = lean_box(0);
v___x_5760_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5758_, v___x_5759_);
lean_dec(v_errorMsg_5758_);
if (v___x_5760_ == 0)
{
lean_dec_ref(v_stxStack_5757_);
lean_dec_ref(v_c_5754_);
lean_dec_ref(v_fn_5753_);
lean_dec(v_kind_5752_);
return v_s_5756_;
}
else
{
lean_object* v___x_5761_; uint8_t v___x_5762_; 
v___x_5761_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5757_);
lean_dec_ref(v_stxStack_5757_);
v___x_5762_ = l_Lean_Syntax_isAntiquots(v___x_5761_);
if (v___x_5762_ == 0)
{
lean_dec_ref(v_c_5754_);
lean_dec_ref(v_fn_5753_);
lean_dec(v_kind_5752_);
return v_s_5756_;
}
else
{
lean_object* v___x_5763_; 
v___x_5763_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5752_, v_fn_5753_, v_c_5754_, v_s_5756_);
return v___x_5763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5764_, lean_object* v_p_5765_, lean_object* v_suffix_5766_){
_start:
{
lean_object* v_info_5767_; lean_object* v_fn_5768_; lean_object* v_info_5769_; lean_object* v_fn_5770_; lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5779_; 
v_info_5767_ = lean_ctor_get(v_p_5765_, 0);
lean_inc_ref(v_info_5767_);
v_fn_5768_ = lean_ctor_get(v_p_5765_, 1);
lean_inc_ref(v_fn_5768_);
lean_dec_ref(v_p_5765_);
v_info_5769_ = lean_ctor_get(v_suffix_5766_, 0);
v_fn_5770_ = lean_ctor_get(v_suffix_5766_, 1);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_suffix_5766_);
if (v_isSharedCheck_5779_ == 0)
{
v___x_5772_ = v_suffix_5766_;
v_isShared_5773_ = v_isSharedCheck_5779_;
goto v_resetjp_5771_;
}
else
{
lean_inc(v_fn_5770_);
lean_inc(v_info_5769_);
lean_dec(v_suffix_5766_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5779_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___f_5774_; lean_object* v___x_5775_; lean_object* v___x_5777_; 
v___f_5774_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5774_, 0, v_fn_5768_);
lean_closure_set(v___f_5774_, 1, v_kind_5764_);
lean_closure_set(v___f_5774_, 2, v_fn_5770_);
v___x_5775_ = l_Lean_Parser_andthenInfo(v_info_5767_, v_info_5769_);
if (v_isShared_5773_ == 0)
{
lean_ctor_set(v___x_5772_, 1, v___f_5774_);
lean_ctor_set(v___x_5772_, 0, v___x_5775_);
v___x_5777_ = v___x_5772_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5778_, 1, v___f_5774_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; 
v___x_5787_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5788_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5789_ = l_Lean_addBuiltinDocString(v___x_5787_, v___x_5788_);
return v___x_5789_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5790_;
v_res_5790_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
stack->m_obj
 = v_res_5790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5791_){
_start:
{
lean_object* v_res_5792_; 
v_res_5792_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5793_, lean_object* v_p_5794_, lean_object* v_suffix_5795_){
_start:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; 
lean_inc_ref(v_p_5794_);
v___x_5796_ = l_Lean_Parser_withoutInfo(v_p_5794_);
lean_inc_ref(v_suffix_5795_);
lean_inc(v_kind_5793_);
v___x_5797_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5793_, v___x_5796_, v_suffix_5795_);
v___x_5798_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5793_, v_p_5794_, v_suffix_5795_);
v___x_5799_ = l_Lean_Parser_withAntiquot(v___x_5797_, v___x_5798_);
return v___x_5799_;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5800_, lean_object* v_kind_5801_, lean_object* v_p_5802_, uint8_t v_anonymous_5803_){
_start:
{
uint8_t v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; 
v___x_5804_ = 0;
lean_inc(v_kind_5801_);
v___x_5805_ = l_Lean_Parser_mkAntiquot(v_name_5800_, v_kind_5801_, v_anonymous_5803_, v___x_5804_);
v___x_5806_ = l_Lean_Parser_node(v_kind_5801_, v_p_5802_);
v___x_5807_ = l_Lean_Parser_withAntiquot(v___x_5805_, v___x_5806_);
return v___x_5807_;
}
}
LEAN_EXPORT void l_Lean_Parser_nodeWithAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_5800_ = stack[0].m_obj;
lean_object* v_kind_5801_ = stack[1].m_obj;
lean_object* v_p_5802_ = stack[2].m_obj;
uint8_t v_anonymous_5803_ = stack[3].m_num;
lean_object* v_res_5808_;
v_res_5808_ = l_Lean_Parser_nodeWithAntiquot(v_name_5800_, v_kind_5801_, v_p_5802_, v_anonymous_5803_);
stack->m_obj
 = v_res_5808_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5809_, lean_object* v_kind_5810_, lean_object* v_p_5811_, lean_object* v_anonymous_5812_){
_start:
{
uint8_t v_anonymous_boxed_5813_; lean_object* v_res_5814_; 
v_anonymous_boxed_5813_ = lean_unbox(v_anonymous_5812_);
v_res_5814_ = l_Lean_Parser_nodeWithAntiquot(v_name_5809_, v_kind_5810_, v_p_5811_, v_anonymous_boxed_5813_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5819_, lean_object* v_sep_5820_){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v_str_5825_; lean_object* v_startInclusive_5826_; lean_object* v_endExclusive_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5821_ = lean_unsigned_to_nat(0u);
v___x_5822_ = lean_string_utf8_byte_size(v_sep_5820_);
v___x_5823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5823_, 0, v_sep_5820_);
lean_ctor_set(v___x_5823_, 1, v___x_5821_);
lean_ctor_set(v___x_5823_, 2, v___x_5822_);
v___x_5824_ = l_String_Slice_trimAscii(v___x_5823_);
v_str_5825_ = lean_ctor_get(v___x_5824_, 0);
lean_inc_ref(v_str_5825_);
v_startInclusive_5826_ = lean_ctor_get(v___x_5824_, 1);
lean_inc(v_startInclusive_5826_);
v_endExclusive_5827_ = lean_ctor_get(v___x_5824_, 2);
lean_inc(v_endExclusive_5827_);
lean_dec_ref(v___x_5824_);
v___x_5828_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5829_ = lean_string_utf8_extract_fast(v_str_5825_, v_startInclusive_5826_, v_endExclusive_5827_);
lean_dec(v_endExclusive_5827_);
lean_dec(v_startInclusive_5826_);
lean_dec_ref(v_str_5825_);
v___x_5830_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5831_ = lean_string_append(v___x_5829_, v___x_5830_);
v___x_5832_ = l_Lean_Parser_symbol(v___x_5831_);
v___x_5833_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5828_, v_p_5819_, v___x_5832_);
return v___x_5833_;
}
}
lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5834_, lean_object* v_sep_5835_, lean_object* v_psep_5836_, uint8_t v_allowTrailingSep_5837_){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = l_Lean_Parser_sepByElemParser(v_p_5834_, v_sep_5835_);
v___x_5839_ = l_Lean_Parser_sepByNoAntiquot(v___x_5838_, v_psep_5836_, v_allowTrailingSep_5837_);
return v___x_5839_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_5834_ = stack[0].m_obj;
lean_object* v_sep_5835_ = stack[1].m_obj;
lean_object* v_psep_5836_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_5837_ = stack[3].m_num;
lean_object* v_res_5840_;
v_res_5840_ = l_Lean_Parser_sepBy(v_p_5834_, v_sep_5835_, v_psep_5836_, v_allowTrailingSep_5837_);
stack->m_obj
 = v_res_5840_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5841_, lean_object* v_sep_5842_, lean_object* v_psep_5843_, lean_object* v_allowTrailingSep_5844_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5845_; lean_object* v_res_5846_; 
v_allowTrailingSep_boxed_5845_ = lean_unbox(v_allowTrailingSep_5844_);
v_res_5846_ = l_Lean_Parser_sepBy(v_p_5841_, v_sep_5842_, v_psep_5843_, v_allowTrailingSep_boxed_5845_);
return v_res_5846_;
}
}
lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5847_, lean_object* v_sep_5848_, lean_object* v_psep_5849_, uint8_t v_allowTrailingSep_5850_){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = l_Lean_Parser_sepByElemParser(v_p_5847_, v_sep_5848_);
v___x_5852_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5851_, v_psep_5849_, v_allowTrailingSep_5850_);
return v___x_5852_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_5847_ = stack[0].m_obj;
lean_object* v_sep_5848_ = stack[1].m_obj;
lean_object* v_psep_5849_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_5850_ = stack[3].m_num;
lean_object* v_res_5853_;
v_res_5853_ = l_Lean_Parser_sepBy1(v_p_5847_, v_sep_5848_, v_psep_5849_, v_allowTrailingSep_5850_);
stack->m_obj
 = v_res_5853_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5854_, lean_object* v_sep_5855_, lean_object* v_psep_5856_, lean_object* v_allowTrailingSep_5857_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5858_; lean_object* v_res_5859_; 
v_allowTrailingSep_boxed_5858_ = lean_unbox(v_allowTrailingSep_5857_);
v_res_5859_ = l_Lean_Parser_sepBy1(v_p_5854_, v_sep_5855_, v_psep_5856_, v_allowTrailingSep_boxed_5858_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5860_, lean_object* v_iniSz_5861_){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; uint8_t v___x_5865_; 
v___x_5862_ = l_Lean_Parser_ParserState_stackSize(v_s_5860_);
v___x_5863_ = lean_unsigned_to_nat(1u);
v___x_5864_ = lean_nat_add(v_iniSz_5861_, v___x_5863_);
v___x_5865_ = lean_nat_dec_eq(v___x_5862_, v___x_5864_);
lean_dec(v___x_5864_);
lean_dec(v___x_5862_);
if (v___x_5865_ == 0)
{
lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5866_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5867_ = l_Lean_Parser_ParserState_mkNode(v_s_5860_, v___x_5866_, v_iniSz_5861_);
return v___x_5867_;
}
else
{
return v_s_5860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5868_, lean_object* v_iniSz_5869_){
_start:
{
lean_object* v_res_5870_; 
v_res_5870_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5868_, v_iniSz_5869_);
lean_dec(v_iniSz_5869_);
return v_res_5870_;
}
}
lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5871_, lean_object* v_tables_5872_, uint8_t v_behavior_5873_, lean_object* v_c_5874_, lean_object* v_s_5875_){
_start:
{
lean_object* v_leadingTable_5876_; lean_object* v_leadingParsers_5877_; lean_object* v_iniSz_5878_; lean_object* v___x_5879_; lean_object* v_fst_5880_; lean_object* v_snd_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_5903_; 
v_leadingTable_5876_ = lean_ctor_get(v_tables_5872_, 0);
lean_inc(v_leadingTable_5876_);
v_leadingParsers_5877_ = lean_ctor_get(v_tables_5872_, 1);
lean_inc(v_leadingParsers_5877_);
lean_dec_ref(v_tables_5872_);
v_iniSz_5878_ = l_Lean_Parser_ParserState_stackSize(v_s_5875_);
lean_inc_ref(v_c_5874_);
v___x_5879_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5876_, v_c_5874_, v_s_5875_, v_behavior_5873_);
lean_dec(v_leadingTable_5876_);
v_fst_5880_ = lean_ctor_get(v___x_5879_, 0);
v_snd_5881_ = lean_ctor_get(v___x_5879_, 1);
v_isSharedCheck_5903_ = !lean_is_exclusive(v___x_5879_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5883_ = v___x_5879_;
v_isShared_5884_ = v_isSharedCheck_5903_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_snd_5881_);
lean_inc(v_fst_5880_);
lean_dec(v___x_5879_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_5903_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v_errorMsg_5885_; lean_object* v___x_5886_; uint8_t v___x_5887_; 
v_errorMsg_5885_ = lean_ctor_get(v_fst_5880_, 4);
v___x_5886_ = lean_box(0);
v___x_5887_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5885_, v___x_5886_);
if (v___x_5887_ == 0)
{
lean_del_object(v___x_5883_);
lean_dec(v_snd_5881_);
lean_dec(v_iniSz_5878_);
lean_dec(v_leadingParsers_5877_);
lean_dec_ref(v_c_5874_);
lean_dec(v_kind_5871_);
return v_fst_5880_;
}
else
{
lean_object* v_ps_5888_; uint8_t v___x_5889_; 
v_ps_5888_ = l_List_appendTR___redArg(v_leadingParsers_5877_, v_snd_5881_);
v___x_5889_ = l_List_isEmpty___redArg(v_ps_5888_);
if (v___x_5889_ == 0)
{
lean_object* v_s_5890_; lean_object* v___x_5891_; 
lean_del_object(v___x_5883_);
lean_dec(v_kind_5871_);
v_s_5890_ = l_Lean_Parser_longestMatchFn(v___x_5886_, v_ps_5888_, v_c_5874_, v_fst_5880_);
v___x_5891_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5890_, v_iniSz_5878_);
lean_dec(v_iniSz_5878_);
return v___x_5891_;
}
else
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5895_; 
lean_dec(v_ps_5888_);
lean_dec(v_iniSz_5878_);
v___x_5892_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5871_, v___x_5889_);
v___x_5893_ = lean_box(0);
lean_inc_ref(v___x_5892_);
if (v_isShared_5884_ == 0)
{
lean_ctor_set_tag(v___x_5883_, 1);
lean_ctor_set(v___x_5883_, 1, v___x_5893_);
lean_ctor_set(v___x_5883_, 0, v___x_5892_);
v___x_5895_ = v___x_5883_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v___x_5893_);
v___x_5895_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
lean_object* v_s_5896_; lean_object* v_errorMsg_5900_; uint8_t v___x_5901_; 
v_s_5896_ = l_Lean_Parser_tokenFn(v___x_5895_, v_c_5874_, v_fst_5880_);
v_errorMsg_5900_ = lean_ctor_get(v_s_5896_, 4);
v___x_5901_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5900_, v___x_5886_);
if (v___x_5901_ == 0)
{
if (v___x_5889_ == 0)
{
goto v___jp_5897_;
}
else
{
lean_dec_ref(v___x_5892_);
return v_s_5896_;
}
}
else
{
goto v___jp_5897_;
}
v___jp_5897_:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5898_ = lean_unsigned_to_nat(0u);
v___x_5899_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5896_, v___x_5892_, v___x_5898_);
return v___x_5899_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_leadingParserAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_5871_ = stack[0].m_obj;
lean_object* v_tables_5872_ = stack[1].m_obj;
uint8_t v_behavior_5873_ = stack[2].m_num;
lean_object* v_c_5874_ = stack[3].m_obj;
lean_object* v_s_5875_ = stack[4].m_obj;
lean_object* v_res_5904_;
v_res_5904_ = l_Lean_Parser_leadingParserAux(v_kind_5871_, v_tables_5872_, v_behavior_5873_, v_c_5874_, v_s_5875_);
stack->m_obj
 = v_res_5904_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5905_, lean_object* v_tables_5906_, lean_object* v_behavior_5907_, lean_object* v_c_5908_, lean_object* v_s_5909_){
_start:
{
uint8_t v_behavior_boxed_5910_; lean_object* v_res_5911_; 
v_behavior_boxed_5910_ = lean_unbox(v_behavior_5907_);
v_res_5911_ = l_Lean_Parser_leadingParserAux(v_kind_5905_, v_tables_5906_, v_behavior_boxed_5910_, v_c_5908_, v_s_5909_);
return v_res_5911_;
}
}
lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5912_, lean_object* v_tables_5913_, uint8_t v_behavior_5914_, lean_object* v_antiquotParser_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; uint8_t v___x_5920_; lean_object* v___x_5921_; 
v___x_5918_ = lean_box(v_behavior_5914_);
v___x_5919_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5919_, 0, v_kind_5912_);
lean_closure_set(v___x_5919_, 1, v_tables_5913_);
lean_closure_set(v___x_5919_, 2, v___x_5918_);
v___x_5920_ = 0;
v___x_5921_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5915_, v___x_5919_, v___x_5920_, v_a_5916_, v_a_5917_);
return v___x_5921_;
}
}
LEAN_EXPORT void l_Lean_Parser_leadingParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_5912_ = stack[0].m_obj;
lean_object* v_tables_5913_ = stack[1].m_obj;
uint8_t v_behavior_5914_ = stack[2].m_num;
lean_object* v_antiquotParser_5915_ = stack[3].m_obj;
lean_object* v_a_5916_ = stack[4].m_obj;
lean_object* v_a_5917_ = stack[5].m_obj;
lean_object* v_res_5922_;
v_res_5922_ = l_Lean_Parser_leadingParser(v_kind_5912_, v_tables_5913_, v_behavior_5914_, v_antiquotParser_5915_, v_a_5916_, v_a_5917_);
stack->m_obj
 = v_res_5922_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5923_, lean_object* v_tables_5924_, lean_object* v_behavior_5925_, lean_object* v_antiquotParser_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_){
_start:
{
uint8_t v_behavior_boxed_5929_; lean_object* v_res_5930_; 
v_behavior_boxed_5929_ = lean_unbox(v_behavior_5925_);
v_res_5930_ = l_Lean_Parser_leadingParser(v_kind_5923_, v_tables_5924_, v_behavior_boxed_5929_, v_antiquotParser_5926_, v_a_5927_, v_a_5928_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5931_, lean_object* v_left_5932_, lean_object* v_ps_5933_, lean_object* v_c_5934_, lean_object* v_s_5935_){
_start:
{
lean_object* v_trailingParsers_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; 
v_trailingParsers_5936_ = lean_ctor_get(v_tables_5931_, 3);
lean_inc(v_trailingParsers_5936_);
lean_dec_ref(v_tables_5931_);
v___x_5937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5937_, 0, v_left_5932_);
v___x_5938_ = l_List_appendTR___redArg(v_ps_5933_, v_trailingParsers_5936_);
v___x_5939_ = l_Lean_Parser_longestMatchFn(v___x_5937_, v___x_5938_, v_c_5934_, v_s_5935_);
return v___x_5939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5940_, lean_object* v_c_5941_, lean_object* v_s_5942_){
_start:
{
lean_object* v_pos_5943_; lean_object* v_trailingTable_5944_; lean_object* v_trailingParsers_5945_; lean_object* v_iniSz_5946_; uint8_t v___x_5947_; lean_object* v___x_5948_; lean_object* v_fst_5949_; lean_object* v_snd_5950_; lean_object* v_stxStack_5951_; lean_object* v_errorMsg_5952_; lean_object* v___x_5967_; uint8_t v___x_5968_; 
v_pos_5943_ = lean_ctor_get(v_s_5942_, 2);
lean_inc(v_pos_5943_);
v_trailingTable_5944_ = lean_ctor_get(v_tables_5940_, 2);
v_trailingParsers_5945_ = lean_ctor_get(v_tables_5940_, 3);
v_iniSz_5946_ = l_Lean_Parser_ParserState_stackSize(v_s_5942_);
v___x_5947_ = 0;
lean_inc_ref(v_c_5941_);
v___x_5948_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5944_, v_c_5941_, v_s_5942_, v___x_5947_);
v_fst_5949_ = lean_ctor_get(v___x_5948_, 0);
lean_inc(v_fst_5949_);
v_snd_5950_ = lean_ctor_get(v___x_5948_, 1);
lean_inc(v_snd_5950_);
lean_dec_ref(v___x_5948_);
v_stxStack_5951_ = lean_ctor_get(v_fst_5949_, 0);
v_errorMsg_5952_ = lean_ctor_get(v_fst_5949_, 4);
v___x_5967_ = lean_box(0);
v___x_5968_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5952_, v___x_5967_);
if (v___x_5968_ == 0)
{
lean_object* v___x_5969_; 
lean_dec(v_snd_5950_);
lean_dec_ref(v_c_5941_);
lean_dec_ref(v_tables_5940_);
v___x_5969_ = l_Lean_Parser_ParserState_restore(v_fst_5949_, v_iniSz_5946_, v_pos_5943_);
lean_dec(v_iniSz_5946_);
return v___x_5969_;
}
else
{
uint8_t v___x_5970_; 
v___x_5970_ = l_List_isEmpty___redArg(v_snd_5950_);
if (v___x_5970_ == 0)
{
goto v___jp_5953_;
}
else
{
uint8_t v___x_5971_; 
v___x_5971_ = l_List_isEmpty___redArg(v_trailingParsers_5945_);
if (v___x_5971_ == 0)
{
goto v___jp_5953_;
}
else
{
lean_dec(v_snd_5950_);
lean_dec(v_iniSz_5946_);
lean_dec(v_pos_5943_);
lean_dec_ref(v_c_5941_);
lean_dec_ref(v_tables_5940_);
return v_fst_5949_;
}
}
}
v___jp_5953_:
{
lean_object* v_left_5954_; lean_object* v_s_5955_; lean_object* v_s_5956_; lean_object* v_pos_5957_; lean_object* v_errorMsg_5958_; lean_object* v___x_5959_; uint8_t v___x_5960_; 
v_left_5954_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5951_);
v_s_5955_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5949_);
lean_inc_ref(v_c_5941_);
lean_inc(v_left_5954_);
lean_inc_ref(v_tables_5940_);
v_s_5956_ = l_Lean_Parser_trailingLoopStep(v_tables_5940_, v_left_5954_, v_snd_5950_, v_c_5941_, v_s_5955_);
v_pos_5957_ = lean_ctor_get(v_s_5956_, 2);
v_errorMsg_5958_ = lean_ctor_get(v_s_5956_, 4);
v___x_5959_ = lean_box(0);
v___x_5960_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5958_, v___x_5959_);
if (v___x_5960_ == 0)
{
uint8_t v_decide_5961_; 
lean_dec_ref(v_c_5941_);
lean_dec_ref(v_tables_5940_);
v_decide_5961_ = lean_nat_dec_eq(v_pos_5957_, v_pos_5943_);
if (v_decide_5961_ == 0)
{
lean_dec(v_left_5954_);
lean_dec(v_iniSz_5946_);
lean_dec(v_pos_5943_);
return v_s_5956_;
}
else
{
lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5962_ = lean_unsigned_to_nat(1u);
v___x_5963_ = lean_nat_sub(v_iniSz_5946_, v___x_5962_);
lean_dec(v_iniSz_5946_);
v___x_5964_ = l_Lean_Parser_ParserState_restore(v_s_5956_, v___x_5963_, v_pos_5943_);
lean_dec(v___x_5963_);
v___x_5965_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5964_, v_left_5954_);
return v___x_5965_;
}
}
else
{
lean_dec(v_left_5954_);
lean_dec(v_iniSz_5946_);
lean_dec(v_pos_5943_);
v_s_5942_ = v_s_5956_;
goto _start;
}
}
}
}
lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5972_, lean_object* v_tables_5973_, uint8_t v_behavior_5974_, lean_object* v_antiquotParser_5975_, lean_object* v_c_5976_, lean_object* v_s_5977_){
_start:
{
lean_object* v_s_5978_; lean_object* v_errorMsg_5979_; lean_object* v___x_5980_; uint8_t v___x_5981_; 
lean_inc_ref(v_c_5976_);
lean_inc_ref(v_tables_5973_);
v_s_5978_ = l_Lean_Parser_leadingParser(v_kind_5972_, v_tables_5973_, v_behavior_5974_, v_antiquotParser_5975_, v_c_5976_, v_s_5977_);
v_errorMsg_5979_ = lean_ctor_get(v_s_5978_, 4);
v___x_5980_ = lean_box(0);
v___x_5981_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5979_, v___x_5980_);
if (v___x_5981_ == 0)
{
lean_dec_ref(v_c_5976_);
lean_dec_ref(v_tables_5973_);
return v_s_5978_;
}
else
{
lean_object* v___x_5982_; 
v___x_5982_ = l_Lean_Parser_trailingLoop(v_tables_5973_, v_c_5976_, v_s_5978_);
return v___x_5982_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_prattParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_5972_ = stack[0].m_obj;
lean_object* v_tables_5973_ = stack[1].m_obj;
uint8_t v_behavior_5974_ = stack[2].m_num;
lean_object* v_antiquotParser_5975_ = stack[3].m_obj;
lean_object* v_c_5976_ = stack[4].m_obj;
lean_object* v_s_5977_ = stack[5].m_obj;
lean_object* v_res_5983_;
v_res_5983_ = l_Lean_Parser_prattParser(v_kind_5972_, v_tables_5973_, v_behavior_5974_, v_antiquotParser_5975_, v_c_5976_, v_s_5977_);
stack->m_obj
 = v_res_5983_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5984_, lean_object* v_tables_5985_, lean_object* v_behavior_5986_, lean_object* v_antiquotParser_5987_, lean_object* v_c_5988_, lean_object* v_s_5989_){
_start:
{
uint8_t v_behavior_boxed_5990_; lean_object* v_res_5991_; 
v_behavior_boxed_5990_ = lean_unbox(v_behavior_5986_);
v_res_5991_ = l_Lean_Parser_prattParser(v_kind_5984_, v_tables_5985_, v_behavior_boxed_5990_, v_antiquotParser_5987_, v_c_5988_, v_s_5989_);
return v_res_5991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5996_, lean_object* v_s_5997_){
_start:
{
lean_object* v_toInputContext_5998_; lean_object* v_pos_5999_; lean_object* v_inputString_6000_; lean_object* v_initStackSz_6001_; uint32_t v_curr_6006_; uint32_t v___x_6007_; uint8_t v___x_6008_; 
v_toInputContext_5998_ = lean_ctor_get(v_c_5996_, 0);
v_pos_5999_ = lean_ctor_get(v_s_5997_, 2);
lean_inc(v_pos_5999_);
v_inputString_6000_ = lean_ctor_get(v_toInputContext_5998_, 0);
v_initStackSz_6001_ = l_Lean_Parser_ParserState_stackSize(v_s_5997_);
v_curr_6006_ = lean_string_utf8_get(v_inputString_6000_, v_pos_5999_);
v___x_6007_ = 48;
v___x_6008_ = lean_uint32_dec_le(v___x_6007_, v_curr_6006_);
if (v___x_6008_ == 0)
{
lean_dec_ref(v_c_5996_);
goto v___jp_6002_;
}
else
{
uint32_t v___x_6009_; uint8_t v___x_6010_; 
v___x_6009_ = 57;
v___x_6010_ = lean_uint32_dec_le(v_curr_6006_, v___x_6009_);
if (v___x_6010_ == 0)
{
lean_dec_ref(v_c_5996_);
goto v___jp_6002_;
}
else
{
uint8_t v___x_6011_; 
v___x_6011_ = lean_uint32_dec_eq(v_curr_6006_, v___x_6007_);
if (v___x_6011_ == 0)
{
lean_object* v___f_6012_; lean_object* v_s_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
lean_dec(v_initStackSz_6001_);
v___f_6012_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_s_6013_ = l_Lean_Parser_takeWhileFn(v___f_6012_, v_c_5996_, v_s_5997_);
v___x_6014_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_6015_ = l_Lean_Parser_mkNodeToken(v___x_6014_, v_pos_5999_, v___x_6010_, v_c_5996_, v_s_6013_);
return v___x_6015_;
}
else
{
lean_dec_ref(v_c_5996_);
goto v___jp_6002_;
}
}
}
v___jp_6002_:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6003_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_6004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6004_, 0, v_initStackSz_6001_);
v___x_6005_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5997_, v___x_6003_, v_pos_5999_, v___x_6004_);
lean_dec_ref_known(v___x_6004_, 1);
return v___x_6005_;
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_6016_; uint8_t v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6016_ = 0;
v___x_6017_ = 1;
v___x_6018_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_6019_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_6020_ = l_Lean_Parser_mkAntiquot(v___x_6019_, v___x_6018_, v___x_6017_, v___x_6016_);
return v___x_6020_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6021_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_6022_ = l_Lean_Parser_mkAtomicInfo(v___x_6021_);
return v___x_6022_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6023_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_6024_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_6025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set(v___x_6025_, 1, v___x_6023_);
return v___x_6025_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
v___x_6026_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_6027_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_6028_ = l_Lean_Parser_withAntiquot(v___x_6027_, v___x_6026_);
return v___x_6028_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_6029_; 
v___x_6029_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_6029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_6030_, lean_object* v_s_6031_){
_start:
{
lean_inc_ref(v_s_6031_);
return v_s_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_6032_, lean_object* v_s_6033_){
_start:
{
lean_object* v_res_6034_; 
v_res_6034_ = l_Lean_Parser_skip___lam__0(v_x_6032_, v_s_6033_);
lean_dec_ref(v_s_6033_);
lean_dec_ref(v_x_6032_);
return v_res_6034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_6040_, lean_object* v_s_6041_, lean_object* v_f_6042_, lean_object* v_b_6043_){
_start:
{
lean_object* v_toApplicative_6044_; lean_object* v_toPure_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; uint8_t v___x_6049_; 
v_toApplicative_6044_ = lean_ctor_get(v_inst_6040_, 0);
v_toPure_6045_ = lean_ctor_get(v_toApplicative_6044_, 1);
v___x_6046_ = l_Lean_Syntax_getArgs(v_s_6041_);
v___x_6047_ = lean_unsigned_to_nat(0u);
v___x_6048_ = lean_array_get_size(v___x_6046_);
v___x_6049_ = lean_nat_dec_lt(v___x_6047_, v___x_6048_);
if (v___x_6049_ == 0)
{
lean_object* v___x_6050_; 
lean_inc(v_toPure_6045_);
lean_dec_ref(v___x_6046_);
lean_dec(v_f_6042_);
lean_dec_ref(v_inst_6040_);
v___x_6050_ = lean_apply_2(v_toPure_6045_, lean_box(0), v_b_6043_);
return v___x_6050_;
}
else
{
lean_object* v___x_6051_; uint8_t v___x_6052_; 
v___x_6051_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_6051_, 0, lean_box(0));
lean_closure_set(v___x_6051_, 1, lean_box(0));
lean_closure_set(v___x_6051_, 2, lean_box(0));
lean_closure_set(v___x_6051_, 3, v_f_6042_);
v___x_6052_ = lean_nat_dec_le(v___x_6048_, v___x_6048_);
if (v___x_6052_ == 0)
{
if (v___x_6049_ == 0)
{
lean_object* v___x_6053_; 
lean_inc(v_toPure_6045_);
lean_dec_ref(v___x_6051_);
lean_dec_ref(v___x_6046_);
lean_dec_ref(v_inst_6040_);
v___x_6053_ = lean_apply_2(v_toPure_6045_, lean_box(0), v_b_6043_);
return v___x_6053_;
}
else
{
size_t v___x_6054_; size_t v___x_6055_; lean_object* v___x_6056_; 
v___x_6054_ = ((size_t)0ULL);
v___x_6055_ = lean_usize_of_nat(v___x_6048_);
v___x_6056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6040_, v___x_6051_, v___x_6046_, v___x_6054_, v___x_6055_, v_b_6043_);
return v___x_6056_;
}
}
else
{
size_t v___x_6057_; size_t v___x_6058_; lean_object* v___x_6059_; 
v___x_6057_ = ((size_t)0ULL);
v___x_6058_ = lean_usize_of_nat(v___x_6048_);
v___x_6059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6040_, v___x_6051_, v___x_6046_, v___x_6057_, v___x_6058_, v_b_6043_);
return v___x_6059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_6060_, lean_object* v_s_6061_, lean_object* v_f_6062_, lean_object* v_b_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6060_, v_s_6061_, v_f_6062_, v_b_6063_);
lean_dec(v_s_6061_);
return v_res_6064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_6065_, lean_object* v_inst_6066_, lean_object* v_00_u03b2_6067_, lean_object* v_s_6068_, lean_object* v_f_6069_, lean_object* v_b_6070_){
_start:
{
lean_object* v___x_6071_; 
v___x_6071_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6066_, v_s_6068_, v_f_6069_, v_b_6070_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_6072_, lean_object* v_inst_6073_, lean_object* v_00_u03b2_6074_, lean_object* v_s_6075_, lean_object* v_f_6076_, lean_object* v_b_6077_){
_start:
{
lean_object* v_res_6078_; 
v_res_6078_ = l_Lean_Syntax_foldArgsM(v_m_6072_, v_inst_6073_, v_00_u03b2_6074_, v_s_6075_, v_f_6076_, v_b_6077_);
lean_dec(v_s_6075_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_6079_, lean_object* v_x1_6080_, lean_object* v_x2_6081_){
_start:
{
lean_object* v___x_6082_; 
v___x_6082_ = lean_apply_2(v_f_6079_, v_x1_6080_, v_x2_6081_);
return v___x_6082_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_6083_, lean_object* v_as_6084_, size_t v_i_6085_, size_t v_stop_6086_, lean_object* v_b_6087_){
_start:
{
uint8_t v___x_6088_; 
v___x_6088_ = lean_usize_dec_eq(v_i_6085_, v_stop_6086_);
if (v___x_6088_ == 0)
{
lean_object* v___x_6089_; lean_object* v___x_6090_; size_t v___x_6091_; size_t v___x_6092_; 
v___x_6089_ = lean_array_uget_borrowed(v_as_6084_, v_i_6085_);
lean_inc(v_f_6083_);
lean_inc(v___x_6089_);
v___x_6090_ = lean_apply_2(v_f_6083_, v___x_6089_, v_b_6087_);
v___x_6091_ = ((size_t)1ULL);
v___x_6092_ = lean_usize_add(v_i_6085_, v___x_6091_);
v_i_6085_ = v___x_6092_;
v_b_6087_ = v___x_6090_;
goto _start;
}
else
{
lean_dec(v_f_6083_);
return v_b_6087_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6083_ = stack[0].m_obj;
lean_object* v_as_6084_ = stack[1].m_obj;
size_t v_i_6085_ = stack[2].m_num;
size_t v_stop_6086_ = stack[3].m_num;
lean_object* v_b_6087_ = stack[4].m_obj;
lean_object* v_res_6094_;
v_res_6094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_6083_, v_as_6084_, v_i_6085_, v_stop_6086_, v_b_6087_);
stack->m_obj
 = v_res_6094_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_6095_, lean_object* v_as_6096_, lean_object* v_i_6097_, lean_object* v_stop_6098_, lean_object* v_b_6099_){
_start:
{
size_t v_i_boxed_6100_; size_t v_stop_boxed_6101_; lean_object* v_res_6102_; 
v_i_boxed_6100_ = lean_unbox_usize(v_i_6097_);
lean_dec(v_i_6097_);
v_stop_boxed_6101_ = lean_unbox_usize(v_stop_6098_);
lean_dec(v_stop_6098_);
v_res_6102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_6095_, v_as_6096_, v_i_boxed_6100_, v_stop_boxed_6101_, v_b_6099_);
lean_dec_ref(v_as_6096_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_6103_, lean_object* v_f_6104_, lean_object* v_b_6105_){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; uint8_t v___x_6109_; 
v___x_6106_ = l_Lean_Syntax_getArgs(v_s_6103_);
v___x_6107_ = lean_unsigned_to_nat(0u);
v___x_6108_ = lean_array_get_size(v___x_6106_);
v___x_6109_ = lean_nat_dec_lt(v___x_6107_, v___x_6108_);
if (v___x_6109_ == 0)
{
lean_dec_ref(v___x_6106_);
lean_dec(v_f_6104_);
return v_b_6105_;
}
else
{
size_t v___x_6110_; size_t v___x_6111_; lean_object* v___x_6112_; 
v___x_6110_ = ((size_t)0ULL);
v___x_6111_ = lean_usize_of_nat(v___x_6108_);
v___x_6112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_6104_, v___x_6106_, v___x_6110_, v___x_6111_, v_b_6105_);
lean_dec_ref(v___x_6106_);
return v___x_6112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_6113_, lean_object* v_f_6114_, lean_object* v_b_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_6113_, v_f_6114_, v_b_6115_);
lean_dec(v_s_6113_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_6117_, lean_object* v_f_6118_, lean_object* v_b_6119_){
_start:
{
lean_object* v___f_6120_; lean_object* v___x_6121_; 
v___f_6120_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6120_, 0, v_f_6118_);
v___x_6121_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_6117_, v___f_6120_, v_b_6119_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_6122_, lean_object* v_f_6123_, lean_object* v_b_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l_Lean_Syntax_foldArgs___redArg(v_s_6122_, v_f_6123_, v_b_6124_);
lean_dec(v_s_6122_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_6126_, lean_object* v_s_6127_, lean_object* v_f_6128_, lean_object* v_b_6129_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l_Lean_Syntax_foldArgs___redArg(v_s_6127_, v_f_6128_, v_b_6129_);
return v___x_6130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_6131_, lean_object* v_s_6132_, lean_object* v_f_6133_, lean_object* v_b_6134_){
_start:
{
lean_object* v_res_6135_; 
v_res_6135_ = l_Lean_Syntax_foldArgs(v_00_u03b2_6131_, v_s_6132_, v_f_6133_, v_b_6134_);
lean_dec(v_s_6132_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_6136_, lean_object* v_s_6137_, lean_object* v_f_6138_, lean_object* v_b_6139_){
_start:
{
lean_object* v___x_6140_; 
v___x_6140_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_6137_, v_f_6138_, v_b_6139_);
return v___x_6140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_6141_, lean_object* v_s_6142_, lean_object* v_f_6143_, lean_object* v_b_6144_){
_start:
{
lean_object* v_res_6145_; 
v_res_6145_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_6141_, v_s_6142_, v_f_6143_, v_b_6144_);
lean_dec(v_s_6142_);
return v_res_6145_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_6146_, lean_object* v_f_6147_, lean_object* v_as_6148_, size_t v_i_6149_, size_t v_stop_6150_, lean_object* v_b_6151_){
_start:
{
lean_object* v___x_6152_; 
v___x_6152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_6147_, v_as_6148_, v_i_6149_, v_stop_6150_, v_b_6151_);
return v___x_6152_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6147_ = stack[1].m_obj;
lean_object* v_as_6148_ = stack[2].m_obj;
size_t v_i_6149_ = stack[3].m_num;
size_t v_stop_6150_ = stack[4].m_num;
lean_object* v_b_6151_ = stack[5].m_obj;
lean_object* v_res_6153_;
v_res_6153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_box(0), v_f_6147_, v_as_6148_, v_i_6149_, v_stop_6150_, v_b_6151_);
stack->m_obj
 = v_res_6153_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_6154_, lean_object* v_f_6155_, lean_object* v_as_6156_, lean_object* v_i_6157_, lean_object* v_stop_6158_, lean_object* v_b_6159_){
_start:
{
size_t v_i_boxed_6160_; size_t v_stop_boxed_6161_; lean_object* v_res_6162_; 
v_i_boxed_6160_ = lean_unbox_usize(v_i_6157_);
lean_dec(v_i_6157_);
v_stop_boxed_6161_ = lean_unbox_usize(v_stop_6158_);
lean_dec(v_stop_6158_);
v_res_6162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_6154_, v_f_6155_, v_as_6156_, v_i_boxed_6160_, v_stop_boxed_6161_, v_b_6159_);
lean_dec_ref(v_as_6156_);
return v_res_6162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_6163_, lean_object* v_s_6164_, lean_object* v_x_6165_){
_start:
{
lean_object* v___x_6166_; 
v___x_6166_ = lean_apply_1(v_f_6163_, v_s_6164_);
return v___x_6166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_6167_, lean_object* v_s_6168_, lean_object* v_f_6169_){
_start:
{
lean_object* v___f_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; 
v___f_6170_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6170_, 0, v_f_6169_);
v___x_6171_ = lean_box(0);
v___x_6172_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6167_, v_s_6168_, v___f_6170_, v___x_6171_);
return v___x_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_6173_, lean_object* v_s_6174_, lean_object* v_f_6175_){
_start:
{
lean_object* v_res_6176_; 
v_res_6176_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6173_, v_s_6174_, v_f_6175_);
lean_dec(v_s_6174_);
return v_res_6176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_6177_, lean_object* v_inst_6178_, lean_object* v_s_6179_, lean_object* v_f_6180_){
_start:
{
lean_object* v___x_6181_; 
v___x_6181_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6178_, v_s_6179_, v_f_6180_);
return v___x_6181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_6182_, lean_object* v_inst_6183_, lean_object* v_s_6184_, lean_object* v_f_6185_){
_start:
{
lean_object* v_res_6186_; 
v_res_6186_ = l_Lean_Syntax_forArgsM(v_m_6182_, v_inst_6183_, v_s_6184_, v_f_6185_);
lean_dec(v_s_6184_);
return v_res_6186_;
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
